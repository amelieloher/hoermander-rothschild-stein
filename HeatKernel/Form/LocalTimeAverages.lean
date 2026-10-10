-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.SteklovRepresentatives
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Local convergence of time averages

Extend an L² function on an open time interval by zero. On a compact subset, short forward
and backward averages are unchanged by this extension. Their global L² convergence therefore
gives local L² convergence of the original averages.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ENNReal

namespace HeatKernel

section AverageFunctions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- On a compact subset of an open set, sufficiently short time averages are unchanged
by extension by zero. -/
theorem exists_pos_timeAverage_indicator_eqOn {I K : Set ℝ} (hI : IsOpen I)
    (hK : IsCompact K) (hKI : K ⊆ I) (u : ℝ → E) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h ∈ Ioo 0 δ,
      EqOn (forwardTimeAverage h (I.indicator u)) (forwardTimeAverage h u) K ∧
      EqOn (backwardTimeAverage h (I.indicator u)) (backwardTimeAverage h u) K := by
  obtain ⟨δ, hδ, hbuffer⟩ := hK.exists_cthickening_subset_open hI hKI
  refine ⟨δ, hδ, ?_⟩
  intro h hh
  constructor
  · intro t ht
    unfold forwardTimeAverage
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le (by linarith [hh.1] : t ≤ t + h)] at hs
    have hst : dist s t ≤ δ := by
      rw [Real.dist_eq, abs_le]
      constructor <;> linarith [hs.1, hs.2, hh.1, hh.2]
    exact indicator_of_mem (hbuffer (mem_cthickening_of_dist_le s t δ K ht hst)) u
  · intro t ht
    unfold backwardTimeAverage
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le (by linarith [hh.1] : t - h ≤ t)] at hs
    have hst : dist s t ≤ δ := by
      rw [Real.dist_eq, abs_le]
      constructor <;> linarith [hs.1, hs.2, hh.1, hh.2]
    exact indicator_of_mem (hbuffer (mem_cthickening_of_dist_le s t δ K ht hst)) u

omit [NormedSpace ℝ E] in
/-- Restricting to a measurable set preserves convergence to zero in an Lp seminorm,
including when the functions agree on that set only for sufficiently late indices. -/
theorem tendsto_eLpNorm_restrict_zero_of_eventually_eqOn {α : Type*} {l : Filter α}
    {f g : α → ℝ → E} {p : ℝ≥0∞} {K : Set ℝ} (hK : MeasurableSet K)
    (hlim : Tendsto (fun a => eLpNorm (g a) p volume) l (𝓝 0))
    (heq : ∀ᶠ a in l, EqOn (f a) (g a) K) :
    Tendsto (fun a => eLpNorm (f a) p (volume.restrict K)) l (𝓝 0) := by
  have hr : Tendsto (fun a => eLpNorm (g a) p (volume.restrict K)) l (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => zero_le) (fun a => eLpNorm_mono_measure (g a) Measure.restrict_le_self)
  apply hr.congr'
  filter_upwards [heq] with a ha
  apply eLpNorm_congr_ae
  filter_upwards [ae_restrict_mem hK] with t ht
  exact (ha ht).symm

end AverageFunctions

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Forward time averages of an L² function on an open set converge in L² on each compact
subset of that open set. -/
theorem tendsto_eLpNorm_forwardTimeAverage_sub_restrict {I K : Set ℝ} (hI : IsOpen I)
    (hK : IsCompact K) (hKI : K ⊆ I) {u : ℝ → E}
    (hu : MemLp u 2 (volume.restrict I)) :
    Tendsto (fun h => eLpNorm (forwardTimeAverage h u - u) 2 (volume.restrict K))
      (𝓝[>] 0) (𝓝 0) := by
  have hext : MemLp (I.indicator u) 2 volume :=
    (memLp_indicator_iff_restrict hI.measurableSet).mpr hu
  obtain ⟨δ, hδ, heq⟩ := exists_pos_timeAverage_indicator_eqOn hI hK hKI u
  apply tendsto_eLpNorm_restrict_zero_of_eventually_eqOn hK.measurableSet
    (tendsto_eLpNorm_forwardTimeAverage_sub_of_memLp hext)
  filter_upwards [Ioo_mem_nhdsGT hδ] with h hh
  intro t ht
  change forwardTimeAverage h u t - u t = forwardTimeAverage h (I.indicator u) t - I.indicator u t
  rw [(heq h hh).1 ht, indicator_of_mem (hKI ht)]

end HeatKernel
