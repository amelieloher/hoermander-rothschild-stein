-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.SignedQuasiCorrection
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- A weight-k coefficient bounded by B times δ^k has a correction
root bounded by B^(1/k) times δ (BB pp. 419–420). -/
theorem quasiCorrection_root_le {a : ℕ} (p : Fin a → ℕ+) (I : List (Fin a))
    (hne : I ≠ []) {b B δ : ℝ} (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hb : |b| ≤ B * δ ^ wordWeight p I) :
    |b| ^ ((wordWeight p I : ℝ)⁻¹) ≤
      B ^ ((wordWeight p I : ℝ)⁻¹) * δ := by
  have hk : wordWeight p I ≠ 0 := by
    have hl : 0 < I.length := List.length_pos_iff.mpr hne
    have hw := length_le_weight p I
    omega
  have hh := Real.rpow_le_rpow (abs_nonneg b) hb
    (by positivity : 0 ≤ (wordWeight p I : ℝ)⁻¹)
  rw [Real.mul_rpow hB (pow_nonneg hδ _), Real.pow_rpow_inv_natCast hδ hk] at hh
  exact hh

end RothschildStein.G3
