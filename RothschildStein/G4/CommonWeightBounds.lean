-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.VolumePolynomial
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Algebra.GroupWithZero

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

/-- Compactness gives a positive minimum and finite maximum of the
finite determinant coefficient sum, provided some frame is nonzero at each
point (BB Def 10.36, p. 515). -/
theorem exists_uniform_coefficient_sum_bounds {E ι : Type*} [TopologicalSpace E] [Fintype ι]
    {K : Set E} (hK : IsCompact K) (lam : ι → E → ℝ)
    (hlam : ∀ i, ContinuousOn (lam i) K) (hnonzero : ∀ x ∈ K, ∃ i, lam i x ≠ 0) :
    ∃ m M : ℝ, 0 < m ∧ 0 < M ∧ ∀ x ∈ K, m ≤ ∑ i, |lam i x| ∧ ∑ i, |lam i x| ≤ M := by
  rcases K.eq_empty_or_nonempty with hEmpty | hne
  · exact ⟨1, 1, zero_lt_one, zero_lt_one, by simp only [hEmpty, mem_empty_iff_false, false_implies, implies_true]⟩
  have hc : ContinuousOn (fun x => ∑ i, |lam i x|) K :=
    continuousOn_finsetSum _ (fun i _ => (hlam i).abs)
  obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hne hc
  obtain ⟨y, hy, hmax⟩ := hK.exists_isMaxOn hne hc
  obtain ⟨i, hi⟩ := hnonzero x hx
  have hpos : 0 < ∑ j, |lam j x| := (abs_pos.mpr hi).trans_le
    (Finset.single_le_sum (fun j _ => abs_nonneg (lam j x)) (Finset.mem_univ i))
  refine ⟨∑ j, |lam j x|, ∑ j, |lam j y|, hpos, hpos.trans_le (hmax hx), ?_⟩
  intro z hz
  exact ⟨hmin hz, hmax hz⟩

/-- Common nonzero frame weights turn the finite polynomial into
uniform r^Q growth on a compact center or center/parameter patch. No
common-weight assertion is inferred from general rank
(BB Def 10.36 and Cor 10.37, pp. 515–516). -/
theorem exists_uniform_commonWeight_polynomial_bounds {E ι : Type*}
    [TopologicalSpace E] [Fintype ι] {K : Set E} (hK : IsCompact K)
    (lam : ι → E → ℝ) (w : ι → ℕ) (Q : ℕ) (hlam : ∀ i, ContinuousOn (lam i) K)
    (hnonzero : ∀ x ∈ K, ∃ i, lam i x ≠ 0)
    (hweight : ∀ x ∈ K, ∀ i, lam i x ≠ 0 → w i = Q) :
    ∃ m M : ℝ, 0 < m ∧ 0 < M ∧ ∀ x ∈ K, ∀ r, 0 ≤ r →
      m * r ^ Q ≤ volumePolynomial (fun i => lam i x) w r ∧
      volumePolynomial (fun i => lam i x) w r ≤ M * r ^ Q := by
  obtain ⟨m, M, hm, hM, hbounds⟩ := exists_uniform_coefficient_sum_bounds hK lam hlam hnonzero
  refine ⟨m, M, hm, hM, ?_⟩
  intro x hx r hr
  rw [volumePolynomial_eq_commonWeight _ w Q (hweight x hx)]
  constructor
  · simpa only [mul_comm] using mul_le_mul_of_nonneg_right (hbounds x hx).1 (pow_nonneg hr Q)
  · simpa only [mul_comm] using mul_le_mul_of_nonneg_right (hbounds x hx).2 (pow_nonneg hr Q)

end RothschildStein.G4
