-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Definitions.fieldDerivative
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.Add

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory

/-- Unit-step Taylor identity with the exact integral remainder
weight. FTC and integration by parts avoid a pointwise remainder choice. -/
theorem unit_taylor_integral (F G H : ℝ → ℝ)
    (hF : ∀ t, HasDerivAt F (G t) t)
    (hG : ∀ t, HasDerivAt G (H t) t) (hH : Continuous H) :
    G 0 = F 1 - F 0 - ∫ t in (0 : ℝ)..1, (1 - t) * H t := by
  have hcG : Continuous G := continuous_iff_continuousAt.mpr fun t => (hG t).continuousAt
  have hi := intervalIntegral.integral_smul_deriv_eq_deriv_smul_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1) (u := fun t : ℝ => 1 - t) (v := G)
    (u' := fun _ : ℝ => -1) (v' := H)
    (continuous_const.sub continuous_id).continuousOn hcG.continuousOn
    (fun t _ => by
      convert! (hasDerivAt_id t).const_sub (1 : ℝ) using 1)
    (fun t _ => hG t) (intervalIntegrable_const) (hH.intervalIntegrable 0 1)
  have ht := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1) (fun t _ => hF t) (hcG.intervalIntegrable 0 1)
  simp only [smul_eq_mul, sub_self, zero_mul, sub_zero, one_mul, neg_one_mul,
    intervalIntegral.integral_neg] at hi
  linarith

/-- The field-action Taylor formula along a prescribed curve follows
from its two chain-rule identities and continuity of the second derivative
along that curve. -/
theorem field_flow_taylor_of_derivative_data {N : ℕ}
    (V : (Fin N → ℝ) → (Fin N → ℝ)) (u : (Fin N → ℝ) → ℝ)
    (γ : ℝ → (Fin N → ℝ)) (x : Fin N → ℝ) (hγ : γ 0 = x)
    (h₁ : ∀ t, HasDerivAt (u ∘ γ) (fieldDerivative V u (γ t)) t)
    (h₂ : ∀ t, HasDerivAt ((fieldDerivative V u) ∘ γ)
      (fieldDerivative V (fieldDerivative V u) (γ t)) t)
    (hc : Continuous ((fieldDerivative V (fieldDerivative V u)) ∘ γ)) :
    fieldDerivative V u x = u (γ 1) - u x -
      ∫ t in (0 : ℝ)..1, (1 - t) * fieldDerivative V (fieldDerivative V u) (γ t) := by
  simpa only [Function.comp_apply, hγ] using
    unit_taylor_integral (u ∘ γ) ((fieldDerivative V u) ∘ γ)
      ((fieldDerivative V (fieldDerivative V u)) ∘ γ) h₁ h₂ hc

end RothschildStein.H3
