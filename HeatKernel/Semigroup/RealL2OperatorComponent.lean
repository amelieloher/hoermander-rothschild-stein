-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Semigroup.RealL2HeatOperators

/-! # Continuous passage from complex operators to their real components -/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped NNReal
namespace HeatKernel
variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

/-- The real component of a complex operator acting on real input. -/
def realL2OperatorComponent (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (l2RealPart μ).comp ((T.restrictScalars ℝ).comp (l2OfReal μ))

theorem realL2OperatorComponent_apply (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (f : Lp ℝ 2 μ) :
    realL2OperatorComponent μ T f = l2RealPart μ (T (l2OfReal μ f)) := rfl

theorem continuous_realL2OperatorComponent : Continuous (realL2OperatorComponent μ) :=
  continuous_const.clm_comp
    ((ContinuousLinearMap.continuous_restrictScalars ℝ).clm_comp continuous_const)

theorem realL2OperatorComponent_heatOperator (R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hpos : R.IsPositive) (hnorm : ‖R‖ ≤ 1) (t : ℝ≥0) :
    realL2OperatorComponent μ (heatOperator (complexL2Extension μ R) t) =
      realL2HeatOperator μ R hpos hnorm t := by
  ext1 f
  rw [realL2OperatorComponent_apply, ← l2OfReal_realL2HeatOperator μ R hpos hnorm,
    l2RealPart_ofReal]

end HeatKernel
