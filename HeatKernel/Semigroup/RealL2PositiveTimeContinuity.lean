-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Semigroup.PositiveTimeContinuity
public import HeatKernel.Semigroup.RealL2OperatorComponent
public import HeatKernel.Semigroup.RealL2PositiveTimeDomain

/-! # Positive-time continuity of real heat and generator operators -/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace HeatKernel
variable {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (hpos : R.IsPositive) (hnorm : ‖R‖ ≤ 1)

theorem continuousAt_realL2HeatOperator_pos {t : ℝ} (ht : 0 < t) :
    ContinuousAt (fun s : ℝ => realL2HeatOperator μ R hpos hnorm s.toNNReal) t := by
  let C := complexL2Extension μ R
  have hspec : spectrum ℝ C ⊆ Icc (0 : ℝ) 1 :=
    spectrum_subset_Icc_of_isPositive_norm_le_one C (complexL2Extension_isPositive μ R hpos)
      (norm_complexL2Extension_le_one μ R hnorm)
  have hc := (continuous_realL2OperatorComponent μ).continuousAt.comp
    (continuousAt_positiveTimeHeatOperator C hspec ht)
  apply hc.congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds ht] with s hs
  rw [Function.comp_apply, ← heatOperator_toNNReal_of_pos C hs,
    realL2OperatorComponent_heatOperator μ R hpos hnorm]

include hpos hnorm in
theorem continuousAt_realL2HeatGeneratorOperator_pos {t : ℝ} (ht : 0 < t) :
    ContinuousAt (realL2HeatGeneratorOperator μ R) t := by
  let C := complexL2Extension μ R
  have hspec : spectrum ℝ C ⊆ Icc (0 : ℝ) 1 :=
    spectrum_subset_Icc_of_isPositive_norm_le_one C (complexL2Extension_isPositive μ R hpos)
      (norm_complexL2Extension_le_one μ R hnorm)
  exact (continuous_realL2OperatorComponent μ).continuousAt.comp
    (continuousAt_heatGeneratorOperator C hspec ht)

end HeatKernel
