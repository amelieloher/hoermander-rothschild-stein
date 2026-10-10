-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueNestedIteration
import Mathlib.Tactic

/-! # Finiteness propagated by nested power iteration -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory
open scoped ENNReal
namespace HeatKernel

/-- A finite starting value and finite multipliers propagate finiteness through an
extended nonnegative recurrence. -/
theorem ennreal_lt_top_of_mul_recurrence {Y a : ℕ → ℝ≥0∞}
    (hY : Y 0 < ⊤) (ha : ∀ j, a j < ⊤)
    (hstep : ∀ j, Y (j + 1) ≤ a j * Y j) : ∀ j, Y j < ⊤ := by
  intro j
  induction j with
  | zero => exact hY
  | succ j hj => exact (hstep j).trans_lt (ENNReal.mul_lt_top (ha j) hj)

/-- The nested norm iteration needs only finite initial L² norm. All later norm
finiteness and the real recurrence follow from the extended norm steps. -/
theorem eLpNormEssSup_le_of_initial_finite_nested_iteration
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (μouter : ℕ → Measure α)
    {f : α → ℝ} {C B δ χ : ℝ}
    (hC : 1 ≤ C) (hB : 1 ≤ B) (hδ : 0 < δ) (hδone : δ ≤ 1) (hχ : 1 < χ)
    (hμ : ∀ j, μ ≤ μouter j)
    (hfinite : eLpNorm f 2 (μouter 0) < ⊤)
    (hstep : ∀ j,
      eLpNorm f (ENNReal.ofReal (2 * χ ^ (j + 1))) (μouter (j + 1)) ≤
        ENNReal.ofReal ((C * B ^ j / δ ^ 2) ^ (1 / (2 * χ ^ j))) *
          eLpNorm f (ENNReal.ofReal (2 * χ ^ j)) (μouter j)) :
    eLpNormEssSup f μ ≤ ENNReal.ofReal
      (Real.exp (((Real.log C - 2 * Real.log δ) / 2) * (1 - χ⁻¹)⁻¹ +
        (Real.log B / 2) * (χ⁻¹ / (1 - χ⁻¹) ^ 2)) *
        (eLpNorm f 2 (μouter 0)).toReal) := by
  have hfin : ∀ j, eLpNorm f (ENNReal.ofReal (2 * χ ^ j)) (μouter j) < ⊤ :=
    ennreal_lt_top_of_mul_recurrence (by simpa using hfinite)
      (fun _ => ENNReal.ofReal_lt_top) hstep
  apply eLpNormEssSup_le_of_finite_nested_cutoff_iteration μ μouter
    hC hB hδ hδone hχ hμ hfin
  intro j
  have hcoef : 0 ≤ (C * B ^ j / δ ^ 2) ^ (1 / (2 * χ ^ j)) := Real.rpow_nonneg
    (by positivity) _
  have hbound := ENNReal.toReal_mono
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hfin j)).ne (hstep j)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hcoef] using hbound

end HeatKernel
