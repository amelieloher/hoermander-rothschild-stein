-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.OperatorInvariance
public import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
attribute [local irreducible] RothschildStein.HomogeneousGroup.inv RothschildStein.HomogeneousGroup.mul
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Left invariance commutes with left translation at any
point where the kernel is differentiable. No globally smooth kernel
extension is required. -/
theorem fieldDerivative_comp_leftTranslation_at
    {V : (Fin N → ℝ) → (Fin N → ℝ)}
    (hV : G2.IsLeftInvariantField G V) {f : (Fin N → ℝ) → ℝ}
    (y x : Fin N → ℝ) (hf : DifferentiableAt ℝ f (G.mul y x)) :
    fieldDerivative V (f ∘ G.mul y) x = fieldDerivative V f (G.mul y x) := by
  unfold fieldDerivative
  rw [fderiv_comp x hf
    ((G2.contDiff_leftTranslation G y).differentiable (by simp)).differentiableAt]
  exact congrArg (fderiv ℝ f (G.mul y x)) (hV y x)

end RothschildStein.H1
