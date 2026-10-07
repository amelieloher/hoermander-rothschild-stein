-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Definitions.fieldDerivative
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Slope

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace RothschildStein.S
variable {n : ℕ}

/-- The derivative of a differentiable test along an
actual integral curve is the field derivative (BB p. 89). -/
theorem hasDerivAt_test_comp_curve
    (X : (Fin n → ℝ) → (Fin n → ℝ)) (φ : (Fin n → ℝ) → ℝ)
    (γ : ℝ → (Fin n → ℝ)) {t : ℝ}
    (hφ : DifferentiableAt ℝ φ (γ t))
    (hγ : HasDerivAt γ (X (γ t)) t) :
    HasDerivAt (fun v => φ (γ v)) (fieldDerivative X φ (γ t)) t := by
  exact hφ.hasFDerivAt.comp_hasDerivAt t hγ

/-- Test difference quotients have the uniform bound
by their field derivative along the entire intervening curve interval,
for either sign of time (BB p. 89). -/
theorem curve_test_difference_quotient_bound
    (X : (Fin n → ℝ) → (Fin n → ℝ)) (φ : (Fin n → ℝ) → ℝ)
    (γ : ℝ → (Fin n → ℝ)) {t M : ℝ} (ht : t ≠ 0)
    (hφ : ∀ s ∈ uIcc 0 t,DifferentiableAt ℝ φ (γ s))
    (hγ : ∀ s ∈ uIcc 0 t,HasDerivAt γ (X (γ s)) s)
    (hM : ∀ s ∈ uIcc 0 t,|fieldDerivative X φ (γ s)| ≤ M) :
    |(φ (γ t)-φ (γ 0))/t| ≤ M := by
  have H := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s hs => (hasDerivAt_test_comp_curve X φ γ (hφ s hs) (hγ s hs)).hasDerivWithinAt)
    (fun s hs => by simpa only [Real.norm_eq_abs] using hM s hs)
    (convex_uIcc 0 t) (left_mem_uIcc : (0 : ℝ) ∈ uIcc 0 t)
    (right_mem_uIcc : t ∈ uIcc 0 t)
  rw [abs_div]
  apply (div_le_iff₀ (abs_pos.mpr ht)).mpr
  simpa only [Real.norm_eq_abs,sub_zero] using H

/-- The test pullback difference quotient converges
to the field derivative at the curve's starting point (BB p. 89). -/
theorem curve_test_difference_quotient_tendsto
    (X : (Fin n → ℝ) → (Fin n → ℝ)) (φ : (Fin n → ℝ) → ℝ)
    (γ : ℝ → (Fin n → ℝ))
    (hφ : DifferentiableAt ℝ φ (γ 0))
    (hγ : HasDerivAt γ (X (γ 0)) 0) :
    Tendsto (fun t => (φ (γ t)-φ (γ 0))/t) (𝓝[≠] 0)
      (𝓝 (fieldDerivative X φ (γ 0))) := by
  simpa only [zero_add,smul_eq_mul,div_eq_mul_inv,mul_comm] using
    (hasDerivAt_test_comp_curve X φ γ hφ hγ).tendsto_slope_zero

end RothschildStein.S
