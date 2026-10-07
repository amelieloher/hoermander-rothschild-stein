-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace RothschildStein.G4

/-- Choose the contraction box after the target lifting radius,
keeping its smallness margin independent of later image shrinkages. -/
theorem exists_small_contraction_radius (s : ℕ) {α d : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hd : 0 < d) :
    ∃ β : ℝ, 0 < β ∧ β ≤ α ∧ β ≤ 1 ∧ 3 * β ≤ d ^ s := by
  refine ⟨min α (d ^ s / 6), lt_min hα (by positivity), min_le_left _ _,
    (min_le_left _ _).trans hα1, ?_⟩
  have hb := min_le_right α (d ^ s / 6)
  have hp : 0 ≤ d ^ s := pow_nonneg hd.le _
  linarith

/-- Choose the new image radius after the old inner-ball radius;
this cannot alter the previously fixed contraction constants. -/
theorem exists_small_transfer_image_radius {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∃ c : ℝ, 0 < c ∧ c < a / 4 ∧ 2 * c < b := by
  refine ⟨min (a / 8) (b / 4), lt_min (by positivity) (by positivity), ?_, ?_⟩
  · exact (min_le_left _ _).trans_lt (by linarith)
  · have hc := min_le_right (a / 8) (b / 4)
    linarith

end RothschildStein.G4
