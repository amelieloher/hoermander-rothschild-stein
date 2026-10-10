-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Function.EssSup
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Local L² bounds on compact cylinders

Continuous functions have finite L² norm on compact sets. Joint continuity
also bounds the spatial L² norm uniformly over a compact time interval.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace HeatKernel

/-- A continuous scalar function on a compact set belongs to L² of the restricted volume. -/
theorem memLp_two_restrict_of_continuousOn_compact {E : Type*}
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [IsFiniteMeasureOnCompacts μ]
    {K : Set E} (hK : IsCompact K) {f : E → ℝ} (hf : ContinuousOn f K) :
    MemLp f 2 (μ.restrict K) := by
  exact (memLp_two_iff_integrable_sq (hf.aestronglyMeasurable hK.measurableSet)).mpr
    ((hf.pow 2).integrableOn_compact hK)

/-- Joint continuity bounds the essential supremum of local spatial L² norms. -/
theorem essSup_spatial_eLpNorm_lt_top_of_continuousOn {n : ℕ}
    {J : Set ℝ} {K : Set (Fin n → ℝ)} (hJ : IsCompact J) (hK : IsCompact K)
    {u : ℝ → (Fin n → ℝ) → ℝ}
    (hu : ContinuousOn (fun z : ℝ × (Fin n → ℝ) => u z.1 z.2) (J ×ˢ K)) :
    essSup (fun t => eLpNorm (u t) 2 (volume.restrict K)) (volume.restrict J) < ⊤ := by
  obtain ⟨C, hC⟩ := (hJ.prod hK).exists_bound_of_continuousOn hu
  have hbound : ∀ t ∈ J, eLpNorm (u t) 2 (volume.restrict K) ≤
      (volume K) ^ (1 / 2 : ℝ) * ENNReal.ofReal C := by
    intro t ht
    have hc : ContinuousOn (u t) K :=
      hu.comp (continuous_const.prodMk continuous_id).continuousOn (fun x hx => ⟨ht, hx⟩)
    have hb := eLpNorm_le_of_ae_bound (p := (2 : ENNReal))
      (hc.aestronglyMeasurable hK.measurableSet)
      (show ∀ᵐ x ∂volume.restrict K, ‖u t x‖ ≤ C from by
        filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
        exact hC (t, x) ⟨ht, hx⟩)
    simpa only [Measure.restrict_apply_univ, ENNReal.toReal_ofNat, one_div] using hb
  refine (essSup_le_of_ae_le ((volume K) ^ (1 / 2 : ℝ) * ENNReal.ofReal C) ?_).trans_lt ?_
  · filter_upwards [ae_restrict_mem hJ.measurableSet] with t ht
    exact hbound t ht
  · exact ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hK.measure_ne_top)
      ENNReal.ofReal_lt_top

end HeatKernel
