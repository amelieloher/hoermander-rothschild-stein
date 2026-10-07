-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.UniformTruncation
public import RothschildStein.H2.BoundedKernelAdjoint

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The jointly measurable positive truncation, using one fixed gauge. -/
def truncatedKernel (d' K : X → X → ℝ) (ε : ℝ) (x y : X) : ℝ :=
  if ε < d' x y then K x y else 0

omit [MetricSpace X] [BorelSpace X] in
/-- Truncation as a kernel agrees with open-shell integral truncation. -/
theorem truncatedKernel_integral {μ : Measure X} {U : Set X} {d' K : X → X → ℝ}
    (hd : Measurable (Function.uncurry d')) (ε : ℝ) (f : X → ℝ) (x : X) :
    (∫ y in U, truncatedKernel d' K ε x y * f y ∂μ) =
      truncatedIntegral μ U d' K ε f x := by
  have hm : MeasurableSet {y | ε < d' x y} :=
    measurableSet_lt measurable_const (hd.comp (measurable_const.prodMk measurable_id))
  have he : (fun y => truncatedKernel d' K ε x y * f y) =
      {y | ε < d' x y}.indicator (fun y => K x y * f y) := by
    funext y
    by_cases hy : ε < d' x y <;> simp [truncatedKernel, hy]
  unfold truncatedIntegral
  rw [he, integral_indicator hm, Measure.restrict_restrict hm, inter_comm]

omit [MetricSpace X] [BorelSpace X] in
/-- Joint measurability is retained by positive truncation. -/
theorem truncatedKernel_measurable {U : Set X} {d' K : X → X → ℝ}
    (hd : Measurable (Function.uncurry d'))
    (hK : Measurable (fun p : U × U => K p.1 p.2)) (ε : ℝ) :
    Measurable (fun p : U × U => truncatedKernel d' K ε p.1 p.2) := by
  have hh : Measurable (fun p : U × U => d' p.1 p.2) := hd.comp ((measurable_subtype_coe.comp measurable_fst).prodMk
    (measurable_subtype_coe.comp measurable_snd))
  exact Measurable.ite (measurableSet_lt measurable_const hh) hK measurable_const

end RothschildStein.H2
