-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.WeightedBoxes

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric

namespace RothschildStein.G4

/-- Positive weights make small controlled coefficient vectors
small in the supremum norm, uniformly in the weights. -/
theorem weighted_coefficients_norm_le {m : ℕ} (w : Fin m → ℕ+)
    {a : Fin m → ℝ} {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (ha : ∀ i, |a i| ≤ δ ^ (w i : ℕ)) : ‖a‖ ≤ δ := by
  apply (pi_norm_le_iff_of_nonneg hδ).mpr
  intro i
  rw [Real.norm_eq_abs]
  exact (ha i).trans (pow_le_of_le_one hδ hδ1 (w i).ne_zero)

/-- Strict weighted boxes lie in the ordinary coefficient ball
when their radius is at most one. -/
theorem weightedBox_subset_ball {m : ℕ} (w : Fin m → ℕ+)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) : weightedBox w r ⊆ ball 0 r := by
  intro a ha
  rw [mem_ball, dist_zero_right]
  apply (pi_norm_lt_iff hr).mpr
  intro i
  rw [Real.norm_eq_abs]
  exact (ha i).trans_le (pow_le_of_le_one hr.le hr1 (w i).ne_zero)

end RothschildStein.G4
