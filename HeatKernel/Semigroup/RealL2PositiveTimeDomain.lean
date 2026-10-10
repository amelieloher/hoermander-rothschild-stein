-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Semigroup.PositiveTimeHeatOperators
public import HeatKernel.Semigroup.RealL2HeatOperators

/-! # The real generator after positive-time heat evolution -/

@[expose] public section
noncomputable section
open MeasureTheory
namespace HeatKernel
variable {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)

/-- The real component of the bounded positive-time generator multiplier. -/
def realL2HeatGeneratorOperator (t : ℝ) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (l2RealPart μ).comp
    (((heatGeneratorOperator (complexL2Extension μ R) t).restrictScalars ℝ).comp (l2OfReal μ))

theorem realL2HeatGeneratorOperator_apply (t : ℝ) (f : Lp ℝ 2 μ) :
    realL2HeatGeneratorOperator μ R t f =
      l2RealPart μ (heatGeneratorOperator (complexL2Extension μ R) t (l2OfReal μ f)) := rfl

theorem realL2HeatOperator_generator_equation (hpos : R.IsPositive) (hnorm : ‖R‖ ≤ 1)
    (t : ℝ) (ht : 0 < t) (f : Lp ℝ 2 μ) :
    R (realL2HeatOperator μ R hpos hnorm t.toNNReal f + realL2HeatGeneratorOperator μ R t f) =
      realL2HeatOperator μ R hpos hnorm t.toNNReal f := by
  let C := complexL2Extension μ R
  have hc := congrArg (l2RealPart μ)
    (positiveTimeHeatOperator_generator_equation C
      (complexL2Extension_isSelfAdjoint μ R hpos.isSelfAdjoint) t (l2OfReal μ f))
  have he : l2RealPart μ (positiveTimeHeatOperator C t (l2OfReal μ f)) =
      realL2HeatOperator μ R hpos hnorm t.toNNReal f := by
    rw [← heatOperator_toNNReal_of_pos C ht, ← l2OfReal_realL2HeatOperator μ R hpos hnorm,
      l2RealPart_ofReal]
  simpa only [C, l2RealPart_complexL2Extension, map_add, he,
    ← realL2HeatGeneratorOperator_apply] using hc

end HeatKernel
