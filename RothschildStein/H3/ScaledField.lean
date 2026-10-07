-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.FlowCurveInterpolation
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3

/-- Field rescaling multiplies its scalar action by the same factor. -/
theorem fieldDerivative_rescale {n : ℕ} (c : ℝ)
    (V : (Fin n → ℝ) → (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) :
    fieldDerivative (c • V) f = c • fieldDerivative V f := by
  funext x
  simp only [fieldDerivative,Pi.smul_apply,map_smul,smul_eq_mul]

/-- Constant scalar multiplication commutes with field differentiation. -/
theorem fieldDerivative_const_smul {n : ℕ} (c : ℝ)
    (V : (Fin n → ℝ) → (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) :
    fieldDerivative V (c • f) = c • fieldDerivative V f := by
  funext x
  simp only [fieldDerivative,fderiv_const_smul_field,Pi.smul_apply,
    smul_apply,smul_eq_mul]

/-- The second action of a rescaled field has the squared factor. -/
theorem fieldDerivative_rescale_square {n : ℕ} (c : ℝ)
    (V : (Fin n → ℝ) → (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) :
    fieldDerivative (c • V) (fieldDerivative (c • V) f) =
      (c*c) • fieldDerivative V (fieldDerivative V f) := by
  rw [fieldDerivative_rescale,fieldDerivative_rescale,fieldDerivative_const_smul,smul_smul]

/-- Reparametrizing a global integral curve by c rescales its field by c. -/
theorem integralCurve_rescale_time {n : ℕ} (c : ℝ)
    (V : (Fin n → ℝ) → (Fin n → ℝ)) (γ : ℝ → (Fin n → ℝ))
    (hγ : IsIntegralCurve γ (fun _ => V)) :
    IsIntegralCurve (fun t => γ (c*t)) (fun _ => c • V) := by
  intro t
  simpa only [Function.comp_def,Pi.smul_apply,mul_one] using
    (hγ (c*t)).scomp t ((hasDerivAt_id t).const_mul c)

end RothschildStein.H3
