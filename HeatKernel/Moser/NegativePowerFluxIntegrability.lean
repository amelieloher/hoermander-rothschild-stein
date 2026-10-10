-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.LogarithmicFluxIntegrability
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import all Mathlib.Basic.Real.Basic

/-! Integrability of shifted reciprocal-power diffusion and cutoff fluxes. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory
namespace HeatKernel

/-- A positive shift bounds every nonpositive real power on nonnegative values,
so multiplication by it preserves square integrability. -/
theorem memLp_shifted_nonpositive_power_mul {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {u g : α → ℝ} {c r : ℝ} (hc : 0 < c) (hr : r ≤ 0)
    (hu : AEStronglyMeasurable u μ) (hupos : ∀ᵐ x ∂μ, 0 ≤ u x)
    (hg : MemLp g 2 μ) : MemLp (fun x => (u x + c) ^ r * g x) 2 μ := by
  apply memLp_two_mul_of_ae_bound (C := c ^ r)
    (((hu.add aestronglyMeasurable_const).aemeasurable.pow_const r).aestronglyMeasurable) hg
  filter_upwards [hupos] with x hx
  change ‖(u x + c) ^ r‖ ≤ c ^ r
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (add_nonneg hx hc.le) r)]
  exact Real.rpow_le_rpow_of_nonpos hc (le_add_of_nonneg_left hx) hr

end HeatKernel
