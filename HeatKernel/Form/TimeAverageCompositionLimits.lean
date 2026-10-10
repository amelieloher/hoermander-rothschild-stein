-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.BochnerRepresentativeCompositionLimits
public import HeatKernel.Form.TimeAverageIntegrability
import Mathlib.Tactic.Linter

/-! # Nonlinear L² convergence of literal local time averages -/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter TopologicalSpace
open scoped NNReal ENNReal Topology

namespace HeatKernel

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] {P : E → F} (hP : Continuous P) {C : ℝ≥0}
    (hb : ∀ u, ‖P u‖ ≤ (C : ℝ) * ‖u‖)
    {I K : Set ℝ} (hI : IsOpen I) (hK : IsCompact K) (hKI : K ⊆ I)
    {u : ℝ → E} (hu : MemLp u 2 (volume.restrict I))

include hP hb hI hK hKI hu

/-- Continuous maps with linear growth preserve the local L² limit of literal forward time averages. -/
theorem tendsto_eLpNorm_comp_forwardTimeAverage_sub_restrict :
    Tendsto (fun h => eLpNorm (fun t => P (forwardTimeAverage h u t) - P (u t))
      2 (volume.restrict K)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  exact tendsto_eLpNorm_continuous_comp_of_eventually_memLp hP hb
    ((eventually_memLp_timeAverages_restrict hI hK hKI hu).mono fun _ hh => hh.1)
    (hu.mono_measure (Measure.restrict_mono_set volume hKI))
    (tendsto_eLpNorm_forwardTimeAverage_sub_restrict hI hK hKI hu)

end HeatKernel
