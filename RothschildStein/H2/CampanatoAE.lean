-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.H2.CampanatoLimit
public import RothschildStein.H2.MaximalEndpoint
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal Topology
namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Comparing a minimiser with the original point value by the
Lebesgue oscillation average (BB Proposition 7.43, p. 330). -/
theorem campanatoConstant_point_bound (P : DoublingPatch X) {α : ℝ} {u : X → ℝ}
    (hu : MemCampanato α P u) {x : X} (hx : x ∈ P.S)
    {r : ℝ} (hr : 0 < r) (hrρ : r ≤ 6 * P.ρ) :
    |campanatoConstant P u x r - u x| ≤ (campanatoSeminorm α P u).toReal * r ^ α +
      (⨍ y in ball x r, |u y - u x| ∂P.μ) := by
  have hv := P.doubling x hx r hr hrρ
  let : IsFiniteMeasure (P.μ.restrict (ball x r)) := ⟨by simpa using hv.2.1⟩
  have hlocal := hu.1.mono_set ((ball_subset_ball hrρ).trans (P.incl x hx))
  have hco := integralOscillation_coercive
    (show IntegrableOn (fun y => u y - u x) (ball x r) P.μ from hlocal.sub (integrable_const _))
    (campanatoConstant P u x r - u x)
  have he : integralOscillation (P.μ.restrict (ball x r))
      (fun y => u y - u x) (campanatoConstant P u x r - u x) =
      integralOscillation (P.μ.restrict (ball x r)) u (campanatoConstant P u x r) := by
    unfold integralOscillation
    apply integral_congr_ae
    filter_upwards [] with y
    congr 1; ring
  rw [he] at hco
  simp only [Measure.restrict_apply_univ] at hco
  have hb := campanatoConstant_integral_bound P hu hx hr hrρ
  have hm : 0 < (P.μ (ball x r)).toReal := ENNReal.toReal_pos hv.1.ne' hv.2.1.ne
  rw [setAverage_eq, smul_eq_mul, measureReal_def]
  have heq : (P.μ (ball x r)).toReal⁻¹ * (∫ y in ball x r, |u y - u x| ∂P.μ) =
      (∫ y in ball x r, |u y - u x| ∂P.μ) / (P.μ (ball x r)).toReal := by ring
  rw [heq]
  apply (mul_le_mul_iff_right₀ hm).mp
  have hdiv := div_mul_cancel₀ (∫ y in ball x r, |u y - u x| ∂P.μ) hm.ne'
  nlinarith

/-- The representative equals the input almost everywhere on S by the patch differentiation theorem (BB Theorem 7.27, pp. 314–316). -/
theorem campanatoRepresentative_ae_eq (P : DoublingPatch X) {α : ℝ} (hα : 0 < α)
    {u : X → ℝ} (hu : MemCampanato α P u) :
    ∀ᵐ x ∂P.μ, x ∈ P.S → campanatoRepresentative P α u x = u x := by
  filter_upwards [P.lebesgue_differentiation u hu.1] with x hx
  intro hxS
  let r := 6 * P.ρ
  have hr : 0 < r := by dsimp [r]; linarith [P.ρ_pos]
  have hrad : Tendsto (campanatoRadius r) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, Eventually.of_forall fun n => (campanatoRadius_facts hr n).1⟩
    change Tendsto (fun n => r * (1 / 2 : ℝ) ^ n) atTop (𝓝 0)
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_mul r
  have havg := (hx hxS).1.comp hrad
  have hpow : Tendsto (fun n => (campanatoRadius r n) ^ α) atTop (𝓝 0) := by
    have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) α)
      (Real.rpow_lt_one (by norm_num) (by norm_num) hα)).const_mul (r ^ α)
    simpa only [campanatoRadius_rpow hr, mul_zero] using hp
  have hbound := (hpow.const_mul (campanatoSeminorm α P u).toReal).add havg
  have hlim := ((campanatoRepresentative_tendsto P hα hu hxS hr le_rfl).sub_const (u x)).abs
  have hle : |campanatoRepresentative P α u x - u x| ≤ 0 := by
    apply le_of_tendsto_of_tendsto hlim (by simpa using hbound)
    exact Eventually.of_forall fun n => campanatoConstant_point_bound P hu hxS
      (campanatoRadius_facts hr n).1 (campanatoRadius_facts hr n).2.1
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hle (abs_nonneg _)))
end RothschildStein.H2
