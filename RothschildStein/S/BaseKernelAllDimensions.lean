-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.SmoothFriedrichsBase
public import RothschildStein.S.MollifierAllDimensions

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Function
namespace RothschildStein.S
variable {n : ℕ}

/-- The base kernel operator is the ordinary mollifier also in
zero dimension; positive dimensions use the established even-kernel
substitution (BB pp. 75–78). -/
theorem baseFriedrichsKernel_op_all_dimensions
    (U : Set (Fin n → ℝ)) (δ : ℝ) (f : (Fin n → ℝ) → ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    friedrichsKernelOp (baseFriedrichsKernel U δ).toFun f ε =
      euclideanRegularize n f ε := by
  cases n with
  | zero =>
    funext x
    rw [euclideanRegularize_zero_dimension f ε]
    unfold friedrichsKernelOp
    change (∫ y, euclideanJ 0 y * f (x+ε • y)) = f x
    have he : ∀ y : Fin 0 → ℝ, x+ε • y = x := fun _ => Subsingleton.elim _ _
    simp_rw [he]
    rw [integral_mul_const,(euclideanJ_normalized 0).2,one_mul]
  | succ n => exact baseFriedrichsKernel_op (Nat.succ_pos n) U δ f hε

/-- The joint smooth base family has precisely the
ordinary mollifier operator, in every dimension (BB p. 75). -/
theorem smoothBaseFriedrichsKernel_op (f : (Fin n → ℝ) → ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    friedrichsKernelOp (smoothBaseFriedrichsKernel n).family f ε =
      euclideanRegularize n f ε := by
  exact baseFriedrichsKernel_op_all_dimensions univ 1 f hε

end RothschildStein.S
