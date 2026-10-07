-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.CommonWeightBounds
public import RothschildStein.G4.VolumeDoubling

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace RothschildStein.G4

/-- The ball-volume comparison gives uniform common-weight ball
volume growth on a compact patch. The same statement applies separately to
original and auxiliary balls; the balls are compared with a common weight
(BB Cor 10.37, pp. 515–516). -/
theorem exists_commonWeight_volume_bounds_of_volumePolynomial_bounds
    {E ι α : Type*} [TopologicalSpace E] [Fintype ι] [MeasurableSpace α]
    {K : Set E} (hK : IsCompact K) (μ : Measure α) (B : E → ℝ → Set α)
    (lam : ι → E → ℝ) (w : ι → ℕ) (Q : ℕ)
    (hlam : ∀ i, ContinuousOn (lam i) K)
    (hnonzero : ∀ x ∈ K, ∃ i, lam i x ≠ 0)
    (hweight : ∀ x ∈ K, ∀ i, lam i x ≠ 0 → w i = Q)
    {c C r₀ : ℝ} (hc : 0 < c) (hC : 0 < C)
    (hvol : ∀ x ∈ K, ∀ r, 0 < r → r ≤ r₀ →
      ENNReal.ofReal (c * volumePolynomial (fun i => lam i x) w r) ≤ μ (B x r) ∧
      μ (B x r) ≤ ENNReal.ofReal (C * volumePolynomial (fun i => lam i x) w r)) :
    ∃ m M : ℝ, 0 < m ∧ 0 < M ∧ ∀ x ∈ K, ∀ r, 0 < r → r ≤ r₀ →
      ENNReal.ofReal (m * r ^ Q) ≤ μ (B x r) ∧ μ (B x r) ≤ ENNReal.ofReal (M * r ^ Q) := by
  obtain ⟨m, M, hm, hM, hpoly⟩ := exists_uniform_commonWeight_polynomial_bounds
    hK lam w Q hlam hnonzero hweight
  refine ⟨c * m, C * M, mul_pos hc hm, mul_pos hC hM, ?_⟩
  intro x hx r hr hrr₀
  obtain ⟨hlo, hhi⟩ := hvol x hx r hr hrr₀
  obtain ⟨hpLo, hpHi⟩ := hpoly x hx r hr.le
  constructor
  · apply le_trans _ hlo
    apply ENNReal.ofReal_le_ofReal
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hpLo hc.le
  · apply hhi.trans
    apply ENNReal.ofReal_le_ofReal
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hpHi hC.le

end RothschildStein.G4
