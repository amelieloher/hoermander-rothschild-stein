-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Semigroup.ScaledFormResolvent
public import Mathlib.Tactic.Module

/-! # The bounded equation for the scaled form resolvent -/

@[expose] public section
noncomputable section
open Set TopologicalSpace
namespace HeatKernel
variable {N q : ℕ} (U : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))

theorem scaledHorizontalFormResolvent_equation
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (U : Set (Fin N → ℝ)))
    (scale : ℝ) (hscale : 0 < scale) (f : SpatialL2 U) :
    horizontalFormResolvent U X (scaledHorizontalFormResolvent U X scale hscale f) +
      scale • (scaledHorizontalFormResolvent U X scale hscale f -
        horizontalFormResolvent U X (scaledHorizontalFormResolvent U X scale hscale f)) =
      horizontalFormResolvent U X f := by
  let u := scaledEnergySolution U X scale hscale f
  let a := energyInclusion U X u
  let R := horizontalFormResolvent U X
  have he (v : energyGraph U X) :
      horizontalEnergy U X u v = inner ℝ (scale⁻¹ • (f - a)) (energyInclusion U X v) := by
    have hv := scaledEnergySolution_equation U X scale hscale f v
    change inner ℝ a (energyInclusion U X v) + scale * horizontalEnergy U X u v =
      inner ℝ f (energyInclusion U X v) at hv
    rw [real_inner_smul_left, inner_sub_left]
    apply mul_left_cancel₀ hscale.ne'
    rw [← mul_assoc, mul_inv_cancel₀ hscale.ne', one_mul]
    linarith only [hv]
  have hr := (horizontalFormEquation_iff_resolvent_eq U X hX u _).mp he
  change R (a + scale⁻¹ • (f - a)) = a at hr
  have hs : scale • a = scale • (R a) + (R f - R a) := by
    calc
      _ = scale • R (a + scale⁻¹ • (f - a)) := congrArg (fun w => scale • w) hr.symm
      _ = _ := by
        rw [map_add, map_smul, map_sub, smul_add, smul_smul,
          mul_inv_cancel₀ hscale.ne', one_smul]
  change R a + scale • (a - R a) = R f
  calc
    _ = (scale • a - scale • R a) + R a := by module
    _ = R f := by rw [hs]; module

end HeatKernel
