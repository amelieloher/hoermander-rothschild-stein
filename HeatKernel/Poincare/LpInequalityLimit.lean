-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import HeatKernel.Poincare.CenteredLpConvergence

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal Topology
namespace HeatKernel

/-- Strong Lp convergence gives convergence of the extended seminorm itself. -/
theorem tendsto_eLpNorm_of_sub
    {A I : Type*} [MeasurableSpace A] {μ : Measure A} {l : Filter I}
    {p : ℝ≥0∞} (hp : 1 ≤ p) {F : I → A → ℝ} {f : A → ℝ}
    (hF : ∀ i, MemLp (F i) p μ) (hf : MemLp f p μ)
    (h : Tendsto (fun i => eLpNorm (F i - f) p μ) l (𝓝 0)) :
    Tendsto (fun i => eLpNorm (F i) p μ) l (𝓝 (eLpNorm f p μ)) := by
  let _ : Fact (1 ≤ p) := ⟨hp⟩
  have H := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' F hF f hf).mpr h
  simpa only [Lp.enorm_toLp] using H.enorm

/-- A fixed finite coefficient is preserved when both sides of an Lp inequality
converge strongly. -/
theorem eLpNorm_le_mul_of_strong_limits
    {A I : Type*} [MeasurableSpace A] {μ : Measure A} {l : Filter I} [NeBot l]
    {p : ℝ≥0∞} (hp : 1 ≤ p) {F H : I → A → ℝ} {f g : A → ℝ}
    (hF : ∀ i, MemLp (F i) p μ) (hH : ∀ i, MemLp (H i) p μ)
    (hf : MemLp f p μ) (hg : MemLp g p μ)
    (hFlim : Tendsto (fun i => eLpNorm (F i - f) p μ) l (𝓝 0))
    (hHlim : Tendsto (fun i => eLpNorm (H i - g) p μ) l (𝓝 0))
    {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hbound : ∀ᶠ i in l, eLpNorm (F i) p μ ≤ C * eLpNorm (H i) p μ) :
    eLpNorm f p μ ≤ C * eLpNorm g p μ := by
  have hleft := tendsto_eLpNorm_of_sub hp hF hf hFlim
  have hright := (ENNReal.continuous_const_mul hC).tendsto (eLpNorm g p μ) |>.comp
    (tendsto_eLpNorm_of_sub hp hH hg hHlim)
  exact le_of_tendsto_of_tendsto hleft hright hbound

/-- Poincaré seminorm inequalities pass through strong convergence without changing
the coefficient, including their moving averages. -/
theorem eLpNorm_mean_oscillation_le_mul_of_strong_limits
    {A I : Type*} [MeasurableSpace A] {μ : Measure A} [IsFiniteMeasure μ]
    {l : Filter I} [NeBot l] {p : ℝ} (hp : 1 ≤ p)
    {F H : I → A → ℝ} {f g : A → ℝ}
    (hF : ∀ i, MemLp (F i) (ENNReal.ofReal p) μ)
    (hH : ∀ i, MemLp (H i) (ENNReal.ofReal p) μ)
    (hf : MemLp f (ENNReal.ofReal p) μ) (hg : MemLp g (ENNReal.ofReal p) μ)
    (hFlim : Tendsto (fun i => eLpNorm (F i - f) (ENNReal.ofReal p) μ) l (𝓝 0))
    (hHlim : Tendsto (fun i => eLpNorm (H i - g) (ENNReal.ofReal p) μ) l (𝓝 0))
    {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hbound : ∀ᶠ i in l, eLpNorm (fun x => F i x - ⨍ y, F i y ∂μ)
      (ENNReal.ofReal p) μ ≤ C * eLpNorm (H i) (ENNReal.ofReal p) μ) :
    eLpNorm (fun x => f x - ⨍ y, f y ∂μ) (ENNReal.ofReal p) μ ≤
      C * eLpNorm g (ENNReal.ofReal p) μ := by
  have hpE : 1 ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp
  exact eLpNorm_le_mul_of_strong_limits hpE
    (fun i => (hF i).sub (memLp_const _)) hH (hf.sub (memLp_const _)) hg
    (tendsto_eLpNorm_sub_averages hp hf.aestronglyMeasurable
      (Eventually.of_forall (fun i => MemLp.integrable hpE (hF i))) hFlim)
    hHlim hC hbound

end HeatKernel
