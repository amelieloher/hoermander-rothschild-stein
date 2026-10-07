-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.H2.CampanatoComparison
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal
namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Comparison at a radius and its half (BB Lemma 7.40, p. 328). -/
theorem DoublingPatch.campanato_halving (P : DoublingPatch X)
    {α : ℝ} (hα : 0 ≤ α) {u : X → ℝ} (hu : MemCampanato α P u)
    {x : X} (hx : x ∈ P.S) {s : ℝ} (hs : 0 < s) (hsρ : s ≤ 6 * P.ρ)
    {c d : ℝ}
    (hc : ∀ e : ℝ, integralOscillation (P.μ.restrict (ball x s)) u c ≤
      integralOscillation (P.μ.restrict (ball x s)) u e)
    (hd : ∀ e : ℝ, integralOscillation (P.μ.restrict (ball x (s / 2))) u d ≤
      integralOscillation (P.μ.restrict (ball x (s / 2))) u e) :
    |c - d| ≤ (P.C_D + 1) * s ^ α * (campanatoSeminorm α P u).toReal := by
  have hhalf : 0 < s / 2 := by linarith
  have hhalfρ : s / 2 ≤ 6 * P.ρ := by linarith
  have hv := P.doubling x hx s hs hsρ
  have hvh := P.doubling x hx (s / 2) hhalf hhalfρ
  have hm : 0 < (P.μ (ball x (s / 2))).toReal := ENNReal.toReal_pos hvh.1.ne' hvh.2.1.ne
  have hvol : (P.μ (ball x s)).toReal ≤ P.C_D * (P.μ (ball x (s / 2))).toReal := by
    have ht := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) hvh.2.1.ne) hv.2.2
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith [P.one_lt_C_D] : 0 ≤ P.C_D)] using ht
  have hpow : (s / 2) ^ α ≤ s ^ α := Real.rpow_le_rpow hhalf.le (by linarith) hα
  have hcmp := oscillation_constants_comparison
    (ball_subset_ball (show s / 2 ≤ s by linarith)) hv.2.1
    (hu.1.mono_set ((ball_subset_ball hsρ).trans (P.incl x hx))) d c
  have hcB := P.oscillation_minimizer_bound hu hx hs hsρ hc
  have hdB := P.oscillation_minimizer_bound hu hx hhalf hhalfρ hd
  have hvB := mul_le_mul_of_nonneg_left hvol
    (mul_nonneg (ENNReal.toReal_nonneg (a := campanatoSeminorm α P u)) (Real.rpow_nonneg hs.le α))
  have hpB := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpow (ENNReal.toReal_nonneg (a := campanatoSeminorm α P u))) hm.le
  rw [abs_sub_comm d c] at hcmp
  nlinarith
end RothschildStein.H2
