-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.LieBracketFiniteSums
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace RothschildStein.L1

/-- Literal sums of actual fields have the ordinary bracket addition rule. -/
theorem lieBracket_fun_add_right {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V W U : E → E) (x : E) (hW : DifferentiableAt ℝ W x) (hU : DifferentiableAt ℝ U x) :
    VectorField.lieBracket ℝ V (fun y => W y + U y) x =
      VectorField.lieBracket ℝ V W x + VectorField.lieBracket ℝ V U x := by
  simp only [VectorField.lieBracket]
  rw [fderiv_fun_add hW hU]
  simp only [add_apply,map_add]
  abel
end RothschildStein.L1
