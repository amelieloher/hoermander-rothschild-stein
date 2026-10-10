-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.ZeroBoundary
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Tactic
import all Mathlib.Basic.Real.Basic
import all Mathlib.Analysis.Normed.Group.Real
import all Mathlib.Analysis.Normed.Field.Basic

/-! Literal moments of time-localized graph values. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace HeatKernel

/-- Almost-everywhere graph representatives preserve every extended value
moment after multiplication by a scalar time cutoff. -/
theorem lintegral_smul_graph_value_rpow_eq {N q : ℕ}
    {V : Opens (Fin N → ℝ)} {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    {τ : Measure ℝ} {Y : ℝ → zeroBoundaryGraph V X} {f : ℝ → (Fin N → ℝ) → ℝ}
    (θ : ℝ → ℝ) (r : ℝ)
    (hrep : ∀ᵐ t ∂τ, (Y t : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] f t) :
    (∫⁻ t, ∫⁻ x, ‖((θ t • Y t : zeroBoundaryGraph V X) : GradientSpace (N := N) ⊤ q).fst x‖ₑ ^ r ∂volume ∂τ) =
      ∫⁻ t, ∫⁻ x, ‖θ t * f t x‖ₑ ^ r ∂volume ∂τ := by
  apply lintegral_congr_ae
  filter_upwards [hrep] with t ht
  apply lintegral_congr_ae
  have hscale := Lp.coeFn_smul (θ t) (Y t : GradientSpace (N := N) ⊤ q).fst
  simp only [Opens.coe_top, Measure.restrict_univ] at hscale
  filter_upwards [ht, hscale] with x hx hs
  change ‖(θ t • (Y t : GradientSpace (N := N) ⊤ q).fst) x‖ₑ ^ r = _
  rw [hs]
  simp only [Pi.smul_apply, smul_eq_mul, hx]

end HeatKernel
