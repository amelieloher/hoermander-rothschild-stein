-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3

/-- The exact power identities for the small scale used to
absorb the near-kernel contribution (BB Proposition 8.53, p. 383). -/
theorem holderInterpolation_scale_powers {a δ M η : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hη1 : η < 1) :
    let t := (η / (2 * max a 1)) ^ (1 / δ)
    0 < t ∧ t < 1 ∧ t ^ δ = η / (2 * max a 1) ∧
      t ^ (-M) = (2 * max a 1) ^ (M / δ) * η ^ (-M / δ) := by
  let b := 2 * max a 1
  have hb : 0 < b := by dsimp [b]; positivity
  have hb2 : 2 ≤ b := by dsimp [b]; linarith [le_max_right a 1]
  have hx : 0 < η / b := div_pos hη hb
  have hx1 : η / b < 1 := (div_lt_one hb).mpr (by linarith)
  dsimp only
  refine ⟨Real.rpow_pos_of_pos hx _, Real.rpow_lt_one hx.le hx1 (div_pos zero_lt_one hδ), ?_, ?_⟩
  · rw [← Real.rpow_mul hx.le]
    simp [hδ.ne', b]
  · rw [← Real.rpow_mul hx.le, Real.div_rpow hη.le hb.le]
    have he : (1 / δ) * -M = -M / δ := by ring
    rw [he, show -M / δ = -(M / δ) by ring, Real.rpow_neg hb.le]
    rw [div_inv_eq_mul]
    dsimp [b]
    ring

end RothschildStein.H3
