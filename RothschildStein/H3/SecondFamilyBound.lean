-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.GlobalSecondWordFromHalfRadius
public import RothschildStein.H3.DriftSecondWeakNorm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory TopologicalSpace
open scoped ENNReal BigOperators

/-- The complete fixed weight-two family has a forcing-only
bound. The input-norm remainder vanishes in the proved exhaustion limit. -/
theorem global_regularity_second_family_bound_of_halfRadius {n q : ℕ}
    (G : HomogeneousGroup n) (ν : G2.HomogeneousNorm G)
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    (K : ℝ) (hK : 0 ≤ K) (hest : HalfRadiusEstimate G ν X p K)
    {u g : (Fin n → ℝ) → ℝ} (hu : MemLp u p (volume : Measure (Fin n → ℝ)))
    (hg : MemLp g p (volume : Measure (Fin n → ℝ)))
    (hlocal : ∀ R : ℝ, 0 < R →
      memSobolevX driftWeight X (quasiballDomain G ν 0 R) 2 p u ∧
      ∃ D : WeakDriftOperatorData X (quasiballDomain G ν 0 R) p u,
        D.operator =ᵐ[volume.restrict (G2.gaugeBall G ν 0 R)] g) :
    driftSecondWeakENorm X ⊤ p u ≤
      ENNReal.ofReal ((driftSecondWordFamily q).card * K) * eLpNorm g p volume := by
  classical
  have hb (I : List (Fin (q + 1))) (hI : I ∈ driftSecondWordFamily q) :
      weakWordENorm X ⊤ I p u ≤ ENNReal.ofReal K * eLpNorm g p volume := by
    obtain ⟨d, hd, _, hdn⟩ := exists_global_secondWord_of_halfRadiusEstimate
      G ν X hp hpt K hK hest hu hg hlocal I ((mem_driftSecondWordFamily_iff I).mp hI)
    rw [S.weakWordENorm_eq X ⊤ I p u d hd]
    simpa only [Opens.coe_top, Measure.restrict_univ, ENNReal.ofReal_mul hK,
      ENNReal.ofReal_toReal hg.eLpNorm_ne_top] using hdn
  unfold driftSecondWeakENorm
  have hs := Finset.sum_le_sum hb
  calc
    _ ≤ ∑ _I ∈ driftSecondWordFamily q, ENNReal.ofReal K * eLpNorm g p volume := hs
    _ = ENNReal.ofReal ((driftSecondWordFamily q).card * K) * eLpNorm g p volume := by
      simp only [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
        ENNReal.ofReal_natCast, mul_assoc]

end RothschildStein.H3
