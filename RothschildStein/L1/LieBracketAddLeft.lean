-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.LieBracketAddRight
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace RothschildStein.L1

/-- Actual brackets distribute over literal addition in the first field. -/
theorem lieBracket_fun_add_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V U W : E → E) (x : E) (hV : DifferentiableAt ℝ V x)
    (hU : DifferentiableAt ℝ U x) :
    VectorField.lieBracket ℝ (fun y => V y + U y) W x =
      VectorField.lieBracket ℝ V W x + VectorField.lieBracket ℝ U W x := by
  simp only [VectorField.lieBracket]
  rw [fderiv_fun_add hV hU]
  simp only [add_apply,map_add]
  abel
end RothschildStein.L1
