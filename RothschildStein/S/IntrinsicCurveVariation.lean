-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.IntrinsicCurveDerivative
public import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter TopologicalSpace
open scoped Topology
namespace RothschildStein.S
variable {n : ℕ}

/-- Intrinsic derivatives bounded along a compact
curve interval bound the variation of the input on that interval.
The curve times can have either order (BB Prop 2.22, pp. 88–90). -/
theorem intrinsic_curve_variation_le
    (Ω : Opens (Fin n → ℝ)) (X : (Fin n → ℝ) → (Fin n → ℝ))
    {f g : (Fin n → ℝ) → ℝ} (hf : hasIntrinsicDeriv Ω X f g)
    (γ : ℝ → (Fin n → ℝ)) {a b M : ℝ}
    (hγ : ∀ t ∈ uIcc a b,IsIntegralCurveAt γ (fun _ => X) t)
    (hm : ∀ t ∈ uIcc a b,γ t ∈ (Ω : Set (Fin n → ℝ)))
    (hM : ∀ t ∈ uIcc a b,|g (γ t)| ≤ M) :
    |f (γ b)-f (γ a)| ≤ M*|b-a| := by
  have H := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hasDerivAt_comp_curve_of_intrinsic_derivative Ω X hf γ
      (hγ t ht) (hm t ht)).hasDerivWithinAt)
    (fun t ht => by simpa only [Real.norm_eq_abs] using hM t ht)
    (convex_uIcc a b) (left_mem_uIcc : a ∈ uIcc a b) (right_mem_uIcc : b ∈ uIcc a b)
  simpa only [Real.norm_eq_abs] using H

/-- Difference quotients along actual integral curves
have the compact-image bound needed for dominated convergence.
The supporting interval includes either time orientation
(BB Prop 2.22, pp. 88–90). -/
theorem intrinsic_curve_difference_quotient_bound
    (Ω : Opens (Fin n → ℝ)) (X : (Fin n → ℝ) → (Fin n → ℝ))
    {f g : (Fin n → ℝ) → ℝ} (hf : hasIntrinsicDeriv Ω X f g)
    (γ : ℝ → (Fin n → ℝ)) {t M : ℝ} (ht : t ≠ 0)
    (hγ : ∀ s ∈ uIcc 0 t,IsIntegralCurveAt γ (fun _ => X) s)
    (hm : ∀ s ∈ uIcc 0 t,γ s ∈ (Ω : Set (Fin n → ℝ)))
    (hM : ∀ s ∈ uIcc 0 t,|g (γ s)| ≤ M) :
    |(f (γ t)-f (γ 0))/t| ≤ M := by
  rw [abs_div]
  apply (div_le_iff₀ (abs_pos.mpr ht)).mpr
  simpa only [sub_zero] using intrinsic_curve_variation_le Ω X hf γ hγ hm hM

end RothschildStein.S
