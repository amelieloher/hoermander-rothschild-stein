-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.Normed.Group.Submodule

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H1
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [AddCommGroup F] [Module ℝ F]

/-- Extend an evaluation functional defined on the range of an
injective operator with the same norm bound (BB Prop 6.2, p. 250;
Hahn–Banach step). -/
theorem exists_boundedFunctional_extension
    (A : F →ₗ[ℝ] E) (hA : Function.Injective A) (ev : F →ₗ[ℝ] ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ u, ‖ev u‖ ≤ C * ‖A u‖) :
    ∃ T : E →L[ℝ] ℝ, ‖T‖ ≤ C ∧ ∀ u, T (A u) = ev u := by
  let e : F ≃ₗ[ℝ] LinearMap.range A := LinearEquiv.ofInjective A hA
  let lam : LinearMap.range A →ₗ[ℝ] ℝ := ev.comp e.symm.toLinearMap
  have hlam (v : LinearMap.range A) : ‖lam v‖ ≤ C * ‖v‖ := by
    change ‖ev (e.symm v)‖ ≤ _
    have H := hb (e.symm v)
    rw [LinearEquiv.ofInjective_symm_apply] at H
    exact H
  let lc : LinearMap.range A →L[ℝ] ℝ :=
    LinearMap.mkContinuous (𝕜 := ℝ) (𝕜₂ := ℝ) lam C hlam
  obtain ⟨T, hT, hnorm⟩ := exists_extension_norm_eq (LinearMap.range A) lc
  refine ⟨T, hnorm.trans_le (lam.mkContinuous_norm_le hC hlam), ?_⟩
  intro u
  have H := hT (e u)
  change T (A u) = ev (e.symm (e u)) at H
  simpa only [LinearEquiv.symm_apply_apply] using H

end RothschildStein.H1
