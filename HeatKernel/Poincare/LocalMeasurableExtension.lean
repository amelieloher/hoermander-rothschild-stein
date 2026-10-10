-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! Measurable zero extensions preserving local continuous differentiability. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter

namespace HeatKernel

/-- Zero extension of a continuous function on an open set is Borel measurable. -/
theorem measurable_indicator_of_continuousOn {E : Type*} [TopologicalSpace E]
    [MeasurableSpace E] [BorelSpace E] {U : Set E} (hU : IsOpen U)
    {f : E → ℝ} (hf : ContinuousOn f U) : Measurable (U.indicator f) := by
  classical
  have he : U.indicator f = U.piecewise f (fun _ => 0) := by
    funext x
    by_cases hx : x ∈ U <;> simp [hx]
  rw [he]
  exact hf.measurable_piecewise (continuousOn_const : ContinuousOn (fun _ : E => (0 : ℝ)) Uᶜ)
      hU.measurableSet

/-- Zero extension agrees with the original function on a neighborhood of each interior
point, so it preserves every local differentiability order there. -/
theorem contDiffAt_indicator_of_isOpen {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} (hU : IsOpen U) {f : E → ℝ} {n : WithTop ℕ∞} {x : E}
    (hx : x ∈ U) (hf : ContDiffOn ℝ n f U) : ContDiffAt ℝ n (U.indicator f) x := by
  classical
  apply ((hf x hx).contDiffAt (hU.mem_nhds hx)).congr_of_eventuallyEq
  filter_upwards [hU.mem_nhds hx] with y hy
  exact indicator_of_mem hy f

/-- The derivative of the zero extension agrees with the original derivative at every
interior point, with no global differentiability hypothesis. -/
theorem fderiv_indicator_of_isOpen {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} (hU : IsOpen U) {f : E → ℝ} {x : E} (hx : x ∈ U) :
    fderiv ℝ (U.indicator f) x = fderiv ℝ f x := by
  classical
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [hU.mem_nhds hx] with y hy
  exact indicator_of_mem hy f

end HeatKernel
