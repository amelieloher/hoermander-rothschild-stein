-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.MeasurableOperatorCurves
public import HeatKernel.Form.MeasurableCurves
public import HeatKernel.Form.BoundedMultiplicationOperators
import Mathlib.Tactic.Linter

/-! # Measurable multiplication of spatial L² curves -/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal

namespace HeatKernel

/-- Jointly measurable bounded coefficients act measurably on a varying spatial L² curve.
The spatial slice assumptions specify an everywhere defined version of the operators. -/
theorem aestronglyMeasurable_boundedL2Mul_curve {T α : Type*}
    [MeasurableSpace T] [MeasurableSpace α] {μ : Measure T} {ν : Measure α} [SFinite ν]
    [SecondCountableTopology (Lp ℝ 2 ν)] {a : T → α → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (ha : AEStronglyMeasurable (Function.uncurry a) (μ.prod ν))
    (has : ∀ t, AEStronglyMeasurable (a t) ν)
    (hb : ∀ t, ∀ᵐ x ∂ν, ‖a t x‖ ≤ C)
    {v : T → Lp ℝ 2 ν} (hv : AEStronglyMeasurable v μ) :
    AEStronglyMeasurable (fun t => boundedL2Mul (has t) hC (hb t) (v t)) μ := by
  borelize ↥(Lp ℝ 2 ν)
  let A : T → Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν :=
    fun t => boundedL2MulContinuousLinearMap (has t) hC (hb t)
  apply aestronglyMeasurable_apply_of_continuous (A := fun t => A t) (fun t => (A t).continuous) _ hv
  intro w
  have hm : AEStronglyMeasurable
      (Function.uncurry (fun t x => a t x * w x)) (μ.prod ν) := by
    simpa only [Pi.mul_def, Function.uncurry_def] using
      ha.mul (Lp.aestronglyMeasurable w).comp_snd
  apply aestronglyMeasurable_L2_of_representatives hm
  exact .of_forall fun t => boundedL2Mul_ae (has t) hC (hb t) w

/-- Uniformly bounded multiplication preserves every Bochner Lp class of spatial L² curves. -/
theorem memLp_boundedL2Mul_curve {T α : Type*}
    [MeasurableSpace T] [MeasurableSpace α] {μ : Measure T} {ν : Measure α} [SFinite ν]
    [SecondCountableTopology (Lp ℝ 2 ν)] {a : T → α → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (ha : AEStronglyMeasurable (Function.uncurry a) (μ.prod ν))
    (has : ∀ t, AEStronglyMeasurable (a t) ν)
    (hb : ∀ t, ∀ᵐ x ∂ν, ‖a t x‖ ≤ C)
    {v : T → Lp ℝ 2 ν} {p : ℝ≥0∞} (hv : MemLp v p μ) :
    MemLp (fun t => boundedL2Mul (has t) hC (hb t) (v t)) p μ := by
  apply (hv.const_smul C).mono
    (aestronglyMeasurable_boundedL2Mul_curve hC ha has hb hv.aestronglyMeasurable)
  apply Eventually.of_forall
  intro t
  simpa only [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg hC] using
    norm_boundedL2Mul_le (has t) hC (hb t) (v t)



end HeatKernel
