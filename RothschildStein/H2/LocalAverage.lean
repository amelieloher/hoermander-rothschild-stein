-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Metric MeasureTheory Filter
open scoped ENNReal Topology

namespace RothschildStein.H2

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The uncentred patch maximal function on the patch, with open balls and
supremum zero when no ball is available (BB Definition 7.24, p. 313). -/
noncomputable def patchMaximal (μ : Measure X) (S : Set X) (ρ : ℝ)
    (f : X → ℝ) (x : X) : ℝ≥0∞ :=
  ⨆ (z ∈ S) (r ∈ Ioc 0 ρ) (_ : dist x z < r),
    ⨍⁻ y in ball z r, ‖f y‖ₑ ∂μ

omit [BorelSpace X] in
/-- Centred small balls are among the balls of the uncentred maximal function. -/
theorem centered_laverage_le_patchMaximal (μ : Measure X) (S : Set X) (ρ : ℝ)
    (f : X → ℝ) {x : X} (hx : x ∈ S) {r : ℝ} (hr : 0 < r) (hrρ : r ≤ ρ) :
    (⨍⁻ y in ball x r, ‖f y‖ₑ ∂μ) ≤ patchMaximal μ S ρ f x := by
  exact le_iSup_of_le x <| le_iSup_of_le hx <| le_iSup_of_le r <|
    le_iSup_of_le ⟨hr, hrρ⟩ <| le_iSup_of_le (by simpa using hr) le_rfl

/-- Continuous functions have uniformly small oscillation on sufficiently
small balls. No assumption about the measure of metric spheres is needed. -/
theorem continuous_eventually_laverage_sub_le (μ : Measure X) (g : X → ℝ)
    {x : X} (hg : ContinuousAt g x) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ),
      (⨍⁻ y in ball x r, ‖g y - g x‖ₑ ∂μ) ≤ ENNReal.ofReal ε := by
  obtain ⟨δ, hδ, hbound⟩ := Metric.continuousAt_iff.mp hg ε hε
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hδ)] with r _ hr
  have hmono : (⨍⁻ y in ball x r, ‖g y - g x‖ₑ ∂μ) ≤
      ⨍⁻ _y in ball x r, ENNReal.ofReal ε ∂μ := by
    apply laverage_mono_ae (ae_restrict_of_forall_mem isOpen_ball.measurableSet
      (fun y hy => ?_))
    rw [Real.enorm_eq_ofReal_abs]
    apply ENNReal.ofReal_le_ofReal
    simpa only [Real.dist_eq] using (hbound ((mem_ball.mp hy).trans hr)).le
  exact hmono.trans ((setLAverage_le_essSup (ball x r) (fun _ => ENNReal.ofReal ε)).trans
    (essSup_le_of_ae_le (ENNReal.ofReal ε) (ae_of_all _ fun _ => le_rfl)))

/-- A continuous approximation controls the differentiation oscillation by
its maximal error, its pointwise error, and its continuous oscillation. -/
theorem laverage_sub_le_approximation (μ : Measure X) (S : Set X) (ρ : ℝ)
    (f g : X → ℝ) {x : X} (hx : x ∈ S) {r : ℝ} (hr : 0 < r) (hrρ : r ≤ ρ)
    (hg : Continuous g) (hball : μ (ball x r) ≠ 0) (hfinite : μ (ball x r) ≠ ⊤) :
    (⨍⁻ y in ball x r, ‖f y - f x‖ₑ ∂μ) ≤
      patchMaximal μ S ρ (f - g) x +
        (⨍⁻ y in ball x r, ‖g y - g x‖ₑ ∂μ) + ‖f x - g x‖ₑ := by
  have hpoint (y : X) : ‖f y - f x‖ₑ ≤
      ‖f y - g y‖ₑ + ‖g y - g x‖ₑ + ‖f x - g x‖ₑ := by
    calc
      ‖f y - f x‖ₑ = ‖(f y - g y) + (g y - g x) - (f x - g x)‖ₑ := by congr 1; ring
      _ ≤ ‖(f y - g y) + (g y - g x)‖ₑ + ‖f x - g x‖ₑ := enorm_sub_le
      _ ≤ _ := add_le_add (enorm_add_le _ _) le_rfl
  calc
    (⨍⁻ y in ball x r, ‖f y - f x‖ₑ ∂μ) ≤
        ⨍⁻ y in ball x r, (‖f y - g y‖ₑ + ‖g y - g x‖ₑ + ‖f x - g x‖ₑ) ∂μ :=
      laverage_mono_ae (ae_of_all _ hpoint)
    _ = (⨍⁻ y in ball x r, ‖f y - g y‖ₑ ∂μ) +
        (⨍⁻ y in ball x r, ‖g y - g x‖ₑ ∂μ) + ‖f x - g x‖ₑ := by
      simp only [setLAverage_eq]
      rw [lintegral_add_right _ measurable_const,
        lintegral_add_right _ (show Measurable (fun y => ‖g y - g x‖ₑ) from
          (hg.sub continuous_const).enorm.measurable),
        ENNReal.add_div, ENNReal.add_div]
      have hc := setLAverage_const hball hfinite ‖f x - g x‖ₑ
      rw [setLAverage_eq] at hc
      rw [hc]
    _ ≤ _ := by
      gcongr
      exact centered_laverage_le_patchMaximal μ S ρ (f - g) hx hr hrρ

end RothschildStein.H2
