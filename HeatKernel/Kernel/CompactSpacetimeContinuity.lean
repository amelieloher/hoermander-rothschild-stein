-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.CompactSpacetimeSlices

/-! # L² continuity of compact spacetime slices

Joint continuity and compact support give a single square-integrable
spatial bound for all slice differences. Dominated convergence then
gives continuity of the L²-valued time curve.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace HeatKernel

/-- Continuous compact spacetime functions have continuous L²-valued spatial slices. -/
theorem continuous_toLp_spatial_slices {n : ℕ}
    (φ : ℝ × (Fin n → ℝ) → ℝ) (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    Continuous (fun t => (memLp_two_spatial_slice φ hφ hc t).toLp
      (fun x => φ (t, x))) := by
  let K : Set (Fin n → ℝ) := Prod.snd '' tsupport φ
  have hK : IsCompact K := hc.image continuous_snd
  obtain ⟨B, hB⟩ := hc.exists_bound_of_continuousOn hφ.continuousOn
  let C : ℝ := max B 0
  have hC : 0 ≤ C := le_max_right _ _
  have hnorm (z : ℝ × (Fin n → ℝ)) : ‖φ z‖ ≤ C := by
    by_cases hz : z ∈ tsupport φ
    · exact (hB z hz).trans (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport hz, norm_zero]
      exact hC
  let g : (Fin n → ℝ) → ℝ := K.indicator (fun _ => 2 * C)
  have hg : MemLp g 2 volume :=
    memLp_indicator_const 2 hK.measurableSet (2 * C) (Or.inr hK.measure_ne_top)
  apply continuous_iff_continuousAt.mpr
  intro a
  apply tendsto_toLp_two_of_dominated_errors (fun t x => φ (t, x))
    (memLp_two_spatial_slice φ hφ hc) (memLp_two_spatial_slice φ hφ hc a) hg
  · exact Eventually.of_forall fun t => Eventually.of_forall fun x => by
      by_cases hx : x ∈ K
      · change ‖φ (t, x) - φ (a, x)‖ ≤ K.indicator (fun _ => 2 * C) x
        rw [Set.indicator_of_mem hx]
        exact (norm_sub_le _ _).trans (by linarith [hnorm (t, x), hnorm (a, x)])
      · have hzero (s : ℝ) : φ (s, x) = 0 :=
          image_eq_zero_of_notMem_tsupport (fun hz => hx ⟨(s, x), hz, rfl⟩)
        change ‖φ (t, x) - φ (a, x)‖ ≤ K.indicator (fun _ => 2 * C) x
        rw [hzero t, hzero a, sub_self, norm_zero, Set.indicator_of_notMem hx]
  · exact Eventually.of_forall fun x =>
      (hφ.comp (continuous_id.prodMk continuous_const)).continuousAt

end HeatKernel
