-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Integral.Average

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace HeatKernel

/-- On a finite measure space, convergence in Lp implies convergence in L1. -/
theorem tendsto_eLpNorm_one_of_finite_measure
    {A I : Type*} [MeasurableSpace A] {μ : Measure A} [IsFiniteMeasure μ]
    {l : Filter I} {p : ℝ} (hp : 1 ≤ p) {F : I → A → ℝ} {f : A → ℝ}
    (hm : ∀ᶠ i in l, AEStronglyMeasurable (F i - f) μ)
    (h : Tendsto (fun i => eLpNorm (F i - f) (ENNReal.ofReal p) μ) l (𝓝 0)) :
    Tendsto (fun i => eLpNorm (F i - f) 1 μ) l (𝓝 0) := by
  have hp0 : 0 ≤ p := zero_le_one.trans hp
  have he : 0 ≤ 1 - 1 / p := sub_nonneg.mpr (by simpa using one_div_le_one_div_of_le zero_lt_one hp)
  have hc : μ univ ^ (1 - 1 / p) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg he (measure_ne_top μ univ)
  have H := (ENNReal.continuous_mul_const hc).tendsto 0 |>.comp h
  simp only [zero_mul] at H
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds H
  · exact Eventually.of_forall (fun _ => zero_le)
  · filter_upwards [hm] with i hi
    simpa only [Function.comp_apply, ENNReal.toReal_one, ENNReal.toReal_ofReal hp0, div_one] using
      eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := ENNReal.ofReal p)
        (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp) hi

/-- Lp convergence of integrable functions on a finite measure space controls their means. -/
theorem tendsto_average_of_eLpNorm_sub
    {A I : Type*} [MeasurableSpace A] {μ : Measure A} [IsFiniteMeasure μ]
    {l : Filter I} {p : ℝ} (hp : 1 ≤ p) {F : I → A → ℝ} {f : A → ℝ}
    (hf : AEStronglyMeasurable f μ)
    (hF : ∀ᶠ i in l, Integrable (F i) μ)
    (h : Tendsto (fun i => eLpNorm (F i - f) (ENNReal.ofReal p) μ) l (𝓝 0)) :
    Tendsto (fun i => ⨍ x, F i x ∂μ) l (𝓝 (⨍ x, f x ∂μ)) := by
  have h1 := tendsto_eLpNorm_one_of_finite_measure hp
    (hF.mono (fun _ hi => hi.aestronglyMeasurable.sub hf)) h
  have hi := tendsto_integral_of_L1' f hF h1
  simpa only [average_eq, smul_eq_mul] using
    (tendsto_const_nhds.mul hi : Tendsto
      (fun i => (μ.real univ)⁻¹ * ∫ x, F i x ∂μ) l
      (𝓝 ((μ.real univ)⁻¹ * ∫ x, f x ∂μ)))

end HeatKernel
