-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic

/-! # Evaluating essential mean-value bounds on continuous solutions -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set
open scoped ENNReal
namespace HeatKernel

/-- An essential norm bound holds pointwise for a continuous function on an open domain. -/
theorem abs_le_of_eLpNormEssSup_le_of_continuousOn
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    {μ : Measure α} [μ.IsOpenPosMeasure] {U : Set α} (hU : IsOpen U)
    {f : α → ℝ} (hf : ContinuousOn f U) {C : ℝ} (hC : 0 ≤ C)
    (hbound : eLpNormEssSup f (μ.restrict U) ≤ ENNReal.ofReal C) :
    ∀ x ∈ U, |f x| ≤ C := by
  have hae : ∀ᵐ x ∂μ.restrict U, |f x| ≤ C := by
    filter_upwards [ae_le_eLpNormEssSup (f := f) (μ := μ.restrict U)] with x hx
    apply (ENNReal.ofReal_le_ofReal_iff hC).mp
    simpa only [Real.enorm_eq_ofReal_abs] using hx.trans hbound
  have heq : (fun x => |f x|) =ᵐ[μ.restrict U] fun x => min |f x| C :=
    hae.mono fun _ hx => (min_eq_left hx).symm
  have heqOn := Measure.eqOn_open_of_ae_eq heq hU hf.abs (hf.abs.inf continuousOn_const)
  intro x hx
  calc
    |f x| = min |f x| C := heqOn hx
    _ ≤ C := min_le_right _ _

/-- Continuous evaluation also preserves the squared form used by heat-kernel bounds. -/
theorem sq_le_of_eLpNormEssSup_le_of_continuousOn
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    {μ : Measure α} [μ.IsOpenPosMeasure] {U : Set α} (hU : IsOpen U)
    {f : α → ℝ} (hf : ContinuousOn f U) {C : ℝ} (hC : 0 ≤ C)
    (hbound : eLpNormEssSup f (μ.restrict U) ≤ ENNReal.ofReal C) :
    ∀ x ∈ U, (f x) ^ 2 ≤ C ^ 2 := by
  intro x hx
  have h := abs_le_of_eLpNormEssSup_le_of_continuousOn hU hf hC hbound x hx
  have ha := (abs_le.mp h)
  nlinarith

end HeatKernel
