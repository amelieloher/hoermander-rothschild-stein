-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.IntrinsicCurveVariation
public import Mathlib.Analysis.Calculus.Deriv.Slope

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter TopologicalSpace
open scoped Topology
namespace RothschildStein.S
variable {n : ℕ}

/-- The inverse-time difference quotient of an intrinsic
function converges to minus its intrinsic derivative along any actual
local integral curve (BB p. 90). -/
theorem intrinsic_curve_inverse_quotient_tendsto
    (Ω : Opens (Fin n → ℝ)) (X : (Fin n → ℝ) → (Fin n → ℝ))
    {f g : (Fin n → ℝ) → ℝ} (hf : hasIntrinsicDeriv Ω X f g)
    (γ : ℝ → (Fin n → ℝ))
    (hγ : IsIntegralCurveAt γ (fun _ => X) 0) (hx : γ 0 ∈ (Ω : Set (Fin n → ℝ))) :
    Tendsto (fun t => (f (γ (-t))-f (γ 0))/t) (𝓝[≠] 0) (𝓝 (-g (γ 0))) := by
  have hd := hasDerivAt_comp_curve_of_intrinsic_derivative Ω X hf γ hγ hx
  have hd' : HasDerivAt (fun s => f (γ s)) (g (γ 0)) (- (0 : ℝ)) := by
    simpa only [neg_zero] using hd
  have H := hd'.scomp (h := fun v : ℝ => -v) 0 (hasDerivAt_id 0).neg
  have H' : HasDerivAt (fun t => f (γ (-t))) (-g (γ 0)) 0 := by
    simpa only [Function.comp_def,smul_eq_mul,neg_one_mul] using H
  simpa only [zero_add,neg_zero,smul_eq_mul,div_eq_mul_inv,mul_comm] using H'.tendsto_slope_zero

/-- The local-flow ODE provides integral curves through each interior point and time (BB pp. 89–90). -/
theorem flow_isIntegralCurveAt
    (X : (Fin n → ℝ) → (Fin n → ℝ)) {τ : ℝ}
    (Φ : ((Fin n → ℝ) × ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ)
    (hsol : ∀ t ∈ Ioo (-τ) τ,HasDerivAt (fun v => Φ (x,v)) (X (Φ (x,t))) t)
    {t : ℝ} (ht : t ∈ Ioo (-τ) τ) :
    IsIntegralCurveAt (fun v => Φ (x,v)) (fun _ => X) t := by
  filter_upwards [isOpen_Ioo.mem_nhds ht] with v hv
  exact hsol v hv

end RothschildStein.S
