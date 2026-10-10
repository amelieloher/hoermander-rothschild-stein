-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace HeatKernel

/-- Continuous functions on compact coordinate sets belong to every Lp space there. -/
theorem memLp_restrict_compact_of_continuousOn
    {N : ℕ} {K : Set (Fin N → ℝ)} (hK : IsCompact K)
    {f : (Fin N → ℝ) → ℝ} (hf : ContinuousOn f K) (p : ℝ≥0∞) :
    MemLp f p (volume.restrict K) := by
  let _ : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf
  exact MemLp.of_bound (hf.aestronglyMeasurable hK.measurableSet) C
    (ae_restrict_of_forall_mem hK.measurableSet hC)

/-- Strong Lp convergence on a larger integration set also holds on a subset. -/
theorem tendsto_eLpNorm_sub_restrict_of_subset
    {A I : Type*} [MeasurableSpace A] {μ : Measure A} {l : Filter I}
    {D K : Set A} (hDK : D ⊆ K) {p : ℝ≥0∞} {F : I → A → ℝ} {f : A → ℝ}
    (h : Tendsto (fun i => eLpNorm (F i - f) p (μ.restrict K)) l (𝓝 0)) :
    Tendsto (fun i => eLpNorm (F i - f) p (μ.restrict D)) l (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
  · exact Filter.Eventually.of_forall (fun _ => zero_le)
  · exact Filter.Eventually.of_forall (fun i =>
      eLpNorm_mono_measure _ (Measure.restrict_mono hDK le_rfl))

end HeatKernel
