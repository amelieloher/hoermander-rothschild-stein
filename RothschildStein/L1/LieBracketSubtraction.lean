-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.LieBracketAddLeft
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace RothschildStein.L1

/-- Actual brackets distribute over literal subtraction on the right. -/
theorem lieBracket_fun_sub_right {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V W U : E → E) (x : E) (hW : DifferentiableAt ℝ W x)
    (hU : DifferentiableAt ℝ U x) :
    VectorField.lieBracket ℝ V (fun y => W y - U y) x =
      VectorField.lieBracket ℝ V W x - VectorField.lieBracket ℝ V U x := by
  simp only [VectorField.lieBracket]
  rw [fderiv_fun_sub hW hU]
  simp only [sub_apply,map_sub]
  abel

/-- Actual brackets distribute over literal subtraction on the left. -/
theorem lieBracket_fun_sub_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V U W : E → E) (x : E) (hV : DifferentiableAt ℝ V x)
    (hU : DifferentiableAt ℝ U x) :
    VectorField.lieBracket ℝ (fun y => V y - U y) W x =
      VectorField.lieBracket ℝ V W x - VectorField.lieBracket ℝ U W x := by
  simp only [VectorField.lieBracket]
  rw [fderiv_fun_sub hV hU]
  simp only [sub_apply,map_sub]
  abel
end RothschildStein.L1
