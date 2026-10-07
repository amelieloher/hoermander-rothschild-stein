-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.OperatorAlgebra

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H1
variable {N : ℕ}

/-- Differentiating the complementary cutoff reverses
its field derivative; the constant term contributes zero. -/
theorem fieldDerivative_one_sub_C1
    (V : (Fin N → ℝ) → (Fin N → ℝ)) {η : (Fin N → ℝ) → ℝ}
    (hη : ContDiff ℝ 1 η) :
    fieldDerivative V (fun w => 1 - η w) = fun w => -fieldDerivative V η w := by
  funext w
  have hd := (hasFDerivAt_const (1 : ℝ) w).sub ((hη.differentiable (by norm_num)).differentiableAt.hasFDerivAt)
  unfold fieldDerivative
  change fderiv ℝ ((fun _ : Fin N → ℝ => (1 : ℝ)) - η) w (V w) = _
  rw [hd.fderiv, zero_sub]
  rfl

end RothschildStein.H1
