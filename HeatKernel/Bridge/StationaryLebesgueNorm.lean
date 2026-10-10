-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic

/-! # Norms of stationary functions on finite time products -/

@[expose] public section
open Set MeasureTheory
open scoped ENNReal
namespace HeatKernel

/-- Holding a spatial L² function constant in time scales its extended norm by
the square root of the total time measure. -/
theorem eLpNorm_two_comp_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) {ν : Measure β} [SFinite ν]
    {f : β → ℝ} (hf : MemLp f 2 ν) :
    eLpNorm (fun z : α × β => f z.2) 2 (μ.prod ν) =
      (μ univ) ^ (1 / 2 : ℝ) * eLpNorm f 2 ν := by
  have hm : AEStronglyMeasurable f (Measure.map Prod.snd (μ.prod ν)) := by
    rw [Measure.map_snd_prod]
    exact hf.aestronglyMeasurable.smul_measure _
  have he := eLpNorm_map_measure (p := (2 : ℝ≥0∞)) hm measurable_snd.aemeasurable
  rw [Measure.map_snd_prod,
    eLpNorm_smul_measure_of_ne_zero_of_ne_top two_ne_zero ENNReal.ofNat_ne_top] at he
  norm_num only [one_div, ENNReal.toReal_inv, ENNReal.toReal_ofNat, smul_eq_mul] at he
  simpa only [one_div, Function.comp_def] using he.symm

/-- The ordinary norm of the stationary L² representative has the same time scaling. -/
theorem norm_toLp_two_comp_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) {ν : Measure β} [IsFiniteMeasure μ] [SFinite ν]
    {f : β → ℝ} (hf : MemLp f 2 ν) :
    ‖(hf.comp_snd μ).toLp (fun z : α × β => f z.2)‖ =
      ((μ univ) ^ (1 / 2 : ℝ)).toReal * ‖hf.toLp f‖ := by
  simp only [Lp.norm_toLp, eLpNorm_two_comp_snd μ hf, ENNReal.toReal_mul]

end HeatKernel
