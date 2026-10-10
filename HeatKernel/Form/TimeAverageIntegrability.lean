-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.LocalTimeAverages
import Mathlib.Tactic.Linter

/-! # Bochner L² membership of literal one-sided time averages -/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter TopologicalSpace
open scoped NNReal ENNReal Topology

namespace HeatKernel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Every nonnegative-length forward average of a global L² curve belongs to L². -/
theorem memLp_forwardTimeAverage {u : ℝ → E} (hu : MemLp u 2 volume) {h : ℝ} (hh : 0 ≤ h) :
    MemLp (forwardTimeAverage h u) 2 volume := by
  have he := forwardTimeAverage_congr_ae hu.coeFn_toLp h
  rw [← he]
  exact (Lp.memLp (steklovForward h (hu.toLp u))).ae_eq (steklovForward_ae_eq hh _)

/-- Every nonnegative-length backward average of a global L² curve belongs to L². -/
theorem memLp_backwardTimeAverage {u : ℝ → E} (hu : MemLp u 2 volume) {h : ℝ} (hh : 0 ≤ h) :
    MemLp (backwardTimeAverage h u) 2 volume := by
  have he := backwardTimeAverage_congr_ae hu.coeFn_toLp h
  rw [← he]
  exact (Lp.memLp (steklovBackward h (hu.toLp u))).ae_eq (steklovBackward_ae_eq hh _)

/-- Literal local forward and backward averages are L² on each compact inner time set for
all sufficiently short positive averaging lengths. -/
theorem eventually_memLp_timeAverages_restrict {I K : Set ℝ} (hI : IsOpen I)
    (hK : IsCompact K) (hKI : K ⊆ I) {u : ℝ → E} (hu : MemLp u 2 (volume.restrict I)) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ), MemLp (forwardTimeAverage h u) 2 (volume.restrict K) ∧
      MemLp (backwardTimeAverage h u) 2 (volume.restrict K) := by
  have hext : MemLp (I.indicator u) 2 volume :=
    (memLp_indicator_iff_restrict hI.measurableSet).mpr hu
  obtain ⟨δ, hδ, heq⟩ := exists_pos_timeAverage_indicator_eqOn hI hK hKI u
  filter_upwards [Ioo_mem_nhdsGT hδ] with h hh
  constructor
  · apply ((memLp_forwardTimeAverage hext hh.1.le).restrict K).ae_eq
    filter_upwards [ae_restrict_mem hK.measurableSet] with t ht
    exact (heq h hh).1 ht
  · apply ((memLp_backwardTimeAverage hext hh.1.le).restrict K).ae_eq
    filter_upwards [ae_restrict_mem hK.measurableSet] with t ht
    exact (heq h hh).2 ht



end HeatKernel
