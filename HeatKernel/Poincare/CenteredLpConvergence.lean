-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.MeanLpConvergence
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal Topology
namespace HeatKernel

/-- Subtracting convergent scalar constants preserves strong Lp convergence on a finite
measure space. -/
theorem tendsto_eLpNorm_sub_constants
    {A I : Type*} [MeasurableSpace A] {μ : Measure A} [IsFiniteMeasure μ]
    {l : Filter I} {p : ℝ} (hp : 1 ≤ p) {F : I → A → ℝ} {f : A → ℝ}
    {c : I → ℝ} {d : ℝ} (hc : Tendsto c l (𝓝 d))
    (h : Tendsto (fun i => eLpNorm (F i - f) (ENNReal.ofReal p) μ) l (𝓝 0)) :
    Tendsto (fun i => eLpNorm
      (fun x => (F i x - c i) - (f x - d)) (ENNReal.ofReal p) μ) l (𝓝 0) := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hpE : 1 ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp
  have hcE : Tendsto (fun i => ‖c i - d‖ₑ) l (𝓝 0) := by
    simpa only [sub_self, enorm_zero] using (hc.sub (tendsto_const_nhds (x := d))).enorm
  have hK : μ univ ^ (1 / (ENNReal.ofReal p).toReal) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) (measure_ne_top μ univ)
  have hconst : Tendsto (fun i => eLpNorm (fun _ : A => c i - d)
      (ENNReal.ofReal p) μ) l (𝓝 0) := by
    have H := (ENNReal.continuous_mul_const hK).tendsto 0 |>.comp hcE
    simpa only [Function.comp_def, zero_mul,
      eLpNorm_const' _ (ENNReal.ofReal_pos.mpr hp0).ne' ENNReal.ofReal_ne_top] using H
  have H := h.add hconst
  simp only [zero_add] at H
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds H
  · exact Eventually.of_forall (fun _ => zero_le)
  · apply Eventually.of_forall
    intro i
    have he : (fun x => (F i x - c i) - (f x - d)) =
        (F i - f) - (fun _ : A => c i - d) := by
      funext x
      simp only [Pi.sub_apply]
      ring
    rw [he]
    exact eLpNorm_sub_le hpE

/-- Centering by the moving average preserves strong Lp convergence. -/
theorem tendsto_eLpNorm_sub_averages
    {A I : Type*} [MeasurableSpace A] {μ : Measure A} [IsFiniteMeasure μ]
    {l : Filter I} {p : ℝ} (hp : 1 ≤ p) {F : I → A → ℝ} {f : A → ℝ}
    (hf : AEStronglyMeasurable f μ) (hF : ∀ᶠ i in l, Integrable (F i) μ)
    (h : Tendsto (fun i => eLpNorm (F i - f) (ENNReal.ofReal p) μ) l (𝓝 0)) :
    Tendsto (fun i => eLpNorm
      (fun x => (F i x - ⨍ y, F i y ∂μ) - (f x - ⨍ y, f y ∂μ))
      (ENNReal.ofReal p) μ) l (𝓝 0) :=
  tendsto_eLpNorm_sub_constants hp (tendsto_average_of_eLpNorm_sub hp hf hF h) h

end HeatKernel
