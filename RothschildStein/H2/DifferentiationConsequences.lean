-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.Differentiation

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Metric MeasureTheory Filter
open scoped ENNReal Topology

namespace RothschildStein.H2

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [BorelSpace X] in
/-- Consequences at each Lebesgue point: convergence of the real
oscillation averages, convergence of the averages of f, and maximal
function domination (BB Theorem 7.27, pp. 314–316). -/
theorem differentiation_consequences
    (μ : Measure X) (S W : Set X) (ρ : ℝ) (hρ : 0 < ρ)
    (hinside : ∀ x ∈ S, ball x (6 * ρ) ⊆ W)
    (hballs : ∀ x ∈ S, ∀ r : ℝ, 0 < r → r ≤ ρ →
      0 < μ (ball x r) ∧ μ (ball x r) < ⊤)
    (f : X → ℝ) (hf : IntegrableOn f W μ) {x : X} (hx : x ∈ S)
    (hlim : Tendsto (fun r : ℝ => ⨍⁻ y in ball x r, ‖f y - f x‖ₑ ∂μ)
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun r : ℝ => ⨍ y in ball x r, |f y - f x| ∂μ) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun r : ℝ => ⨍ y in ball x r, f y ∂μ) (𝓝[>] 0) (𝓝 (f x)) ∧
    ‖f x‖ₑ ≤ patchMaximal μ S ρ f x := by
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r ∧ r ≤ ρ := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hρ)] with r hr hrρ
    exact ⟨hr, hrρ.le⟩
  have hlocal (r : ℝ) (hr : 0 < r) (hrρ : r ≤ ρ) : IntegrableOn f (ball x r) μ :=
    hf.mono_set ((ball_subset_ball (by linarith)).trans (hinside x hx))
  have hnorm : Tendsto (fun r : ℝ => ⨍ y in ball x r, ‖f y - f x‖ ∂μ)
      (𝓝[>] 0) (𝓝 0) := by
    have ht := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim
    simp only [ENNReal.toReal_zero] at ht
    apply ht.congr'
    filter_upwards [hev] with r hr
    have he : IntegrableOn (fun y => f y - f x) (ball x r) μ :=
      (hlocal r hr.1 hr.2).sub (integrableOn_const (hballs x hx r hr.1 hr.2).2.ne)
    change (⨍⁻ y in ball x r, ‖f y - f x‖ₑ ∂μ).toReal = _
    rw [toReal_setLAverage he.aestronglyMeasurable.enorm (ae_of_all _ (fun _ => enorm_ne_top))]
    simp only [toReal_enorm]
  have havg : Tendsto (fun r : ℝ => ⨍ y in ball x r, f y ∂μ) (𝓝[>] 0) (𝓝 (f x)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hnorm
    filter_upwards [hev] with r hr
    have hb := hballs x hx r hr.1 hr.2
    nth_rw 1 [← setAverage_const hb.1.ne' hb.2.ne (f x)]
    simp_rw [setAverage_eq']
    rw [← integral_sub]
    · exact norm_integral_le_integral_norm _
    · exact (integrable_inv_smul_measure hb.1.ne' hb.2.ne).2 (hlocal r hr.1 hr.2)
    · exact (integrable_inv_smul_measure hb.1.ne' hb.2.ne).2 (integrableOn_const hb.2.ne)
  refine ⟨by simpa only [Real.norm_eq_abs] using hnorm, havg, ?_⟩
  apply le_of_tendsto havg.enorm
  filter_upwards [hev] with r hr
  calc
    ‖⨍ y in ball x r, f y ∂μ‖ₑ ≤ ⨍⁻ y in ball x r, ‖f y‖ₑ ∂μ :=
      enorm_integral_le_lintegral_enorm f
    _ ≤ patchMaximal μ S ρ f x := centered_laverage_le_patchMaximal μ S ρ f hx hr.1 hr.2

/-- Full patch Lebesgue differentiation statement, including
convergence of the function averages and maximal domination from the weak (1,1) maximal bound (BB Theorem 7.27, pp. 314–316). -/
theorem lebesgue_differentiation_of_maximal_weak_type
    (μ : Measure X) (S W : Set X) (ρ C : ℝ) (hρ : 0 < ρ)
    (hinside : ∀ x ∈ S, ball x (6 * ρ) ⊆ W)
    (hballs : ∀ x ∈ S, ∀ r : ℝ, 0 < r → r ≤ ρ →
      0 < μ (ball x r) ∧ μ (ball x r) < ⊤)
    (hW : MeasurableSet W ∧ μ W < ⊤) (hweak : PatchMaximalWeakType μ S W ρ C)
    (f : X → ℝ) (hf : IntegrableOn f W μ) :
    ∀ᵐ x ∂μ, x ∈ S →
      Tendsto (fun r : ℝ => ⨍ y in ball x r, |f y - f x| ∂μ) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun r : ℝ => ⨍ y in ball x r, f y ∂μ) (𝓝[>] 0) (𝓝 (f x)) ∧
      ‖f x‖ₑ ≤ patchMaximal μ S ρ f x := by
  filter_upwards [ae_tendsto_laverage_sub_of_maximal_weak_type μ S W ρ C hρ hinside hballs
    hW hweak f hf] with x hx hxS
  exact differentiation_consequences μ S W ρ hρ hinside hballs f hf hxS (hx hxS)

end RothschildStein.H2
