-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Function.Holder
public import HeatKernel.Form.TimeAverages

/-! # Strong L² limits of dual pairings

The Hölder pairing is a continuous bilinear map on two L² spaces. Strong convergence
of a dual flux and a test curve therefore gives convergence of their integrated pairing.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace HeatKernel

/-- Strong L² convergence of a dual-valued curve and a test curve implies convergence
of the integral of their pointwise evaluation. -/
theorem tendsto_integral_dual_apply_of_tendsto_L2 {α ι E : Type*}
    [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {l : Filter ι} {F : ι → Lp (E →L[ℝ] ℝ) 2 μ} {v : ι → Lp E 2 μ}
    {F₀ : Lp (E →L[ℝ] ℝ) 2 μ} {v₀ : Lp E 2 μ}
    (hF : Tendsto F l (𝓝 F₀)) (hv : Tendsto v l (𝓝 v₀)) :
    Tendsto (fun i => ∫ x, F i x (v i x) ∂μ) l (𝓝 (∫ x, F₀ x (v₀ x) ∂μ)) := by
  let B := ContinuousLinearMap.id ℝ (E →L[ℝ] ℝ)
  have H := ((B.lpPairing μ 2 2).continuous₂.tendsto (F₀, v₀)).comp (hF.prodMk_nhds hv)
  simpa only [Function.comp_def, Function.uncurry_def, ContinuousLinearMap.lpPairing_eq_integral,
    B, ContinuousLinearMap.id_apply] using H

end HeatKernel
