-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.H2.CampanatoConstants
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal
namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MeasurableSpace X] [BorelSpace X] in
/-- The two-radius intersection contains the smaller centre balls.
BB Lemma 7.44, pp. 330–331 uses open balls throughout. -/
theorem campanato_intersection_ball {x y : X} {r : ℝ} (hxy : dist x y = r) :
    ball x r ⊆ ball x (2 * r) ∩ ball y (2 * r) := by
  intro z hz
  have hzx : dist z x < r := hz
  have hzxy := dist_triangle z x y
  refine ⟨?_, ?_⟩ <;> change dist z _ < 2 * r <;> linarith [dist_nonneg (x := x) (y := y)]

/-- Comparison of minimisers at neighbouring centres (BB Lemma 7.44). -/
theorem campanatoConstant_centres (P : DoublingPatch X) {α : ℝ}
    {u : X → ℝ} (hu : MemCampanato α P u) {x y : X}
    (hx : x ∈ P.S) (hy : y ∈ P.S) {r : ℝ} (hr : 0 < r)
    (hxy : dist x y = r) (hrρ : 2 * r ≤ 6 * P.ρ) :
    |campanatoConstant P u x (2 * r) - campanatoConstant P u y (2 * r)| ≤
      2 * P.C_D * (2 * r) ^ α * (campanatoSeminorm α P u).toReal := by
  let I := ball x (2 * r) ∩ ball y (2 * r)
  have hvx := P.doubling x hx (2 * r) (by positivity) hrρ
  have hvy := P.doubling y hy (2 * r) (by positivity) hrρ
  have hvxr := P.doubling x hx r hr (by linarith)
  have hsubx : ball x r ⊆ I := campanato_intersection_ball hxy
  have hsuby : ball y r ⊆ I := by
    rw [show I = ball y (2 * r) ∩ ball x (2 * r) from inter_comm _ _]
    exact campanato_intersection_ball (by simpa only [dist_comm] using hxy)
  have hIt : P.μ I < ⊤ := (measure_mono inter_subset_left).trans_lt hvx.2.1
  have hIp : 0 < P.μ I := hvxr.1.trans_le (measure_mono hsubx)
  have hm : 0 < (P.μ I).toReal := ENNReal.toReal_pos hIp.ne' hIt.ne
  have hxI : (P.μ (ball x (2 * r))).toReal ≤ P.C_D * (P.μ I).toReal := by
    have hd := hvx.2.2
    rw [show 2 * r / 2 = r by ring] at hd
    have hh := hd.trans (mul_le_mul_right (measure_mono hsubx) _)
    have ht := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hIt.ne) hh
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith [P.one_lt_C_D] : 0 ≤ P.C_D)] using ht
  have hyI : (P.μ (ball y (2 * r))).toReal ≤ P.C_D * (P.μ I).toReal := by
    have hd := hvy.2.2
    rw [show 2 * r / 2 = r by ring] at hd
    have hh := hd.trans (mul_le_mul_right (measure_mono hsuby) _)
    have ht := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hIt.ne) hh
    simpa only [ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by linarith [P.one_lt_C_D] : 0 ≤ P.C_D)] using ht
  have huY := hu.1.mono_set ((ball_subset_ball hrρ).trans (P.incl y hy))
  have huX := hu.1.mono_set ((ball_subset_ball hrρ).trans (P.incl x hx))
  have hcmp := oscillation_constants_comparison (show I ⊆ ball y (2 * r) from inter_subset_right)
    hvy.2.1 huY (campanatoConstant P u x (2 * r)) (campanatoConstant P u y (2 * r))
  have hmon := setIntegral_mono_set
    (huX.sub (integrableOn_const (C := campanatoConstant P u x (2 * r)) hvx.2.1.ne)).abs
    (ae_of_all _ fun _ => abs_nonneg _) (ae_of_all _ (show I ⊆ ball x (2 * r) from inter_subset_left))
  have hbx := campanatoConstant_integral_bound P hu hx (show 0 < 2 * r by positivity) hrρ
  have hby := campanatoConstant_integral_bound P hu hy (show 0 < 2 * r by positivity) hrρ
  have hxB := mul_le_mul_of_nonneg_left hxI
    (mul_nonneg (ENNReal.toReal_nonneg (a := campanatoSeminorm α P u)) (Real.rpow_nonneg (show 0 ≤ 2 * r by positivity) α))
  have hyB := mul_le_mul_of_nonneg_left hyI
    (mul_nonneg (ENNReal.toReal_nonneg (a := campanatoSeminorm α P u)) (Real.rpow_nonneg (show 0 ≤ 2 * r by positivity) α))
  change (∫ z in I, |u z - campanatoConstant P u x (2 * r)| ∂P.μ) ≤ _ at hmon
  change _ ≤ (∫ z in I, |u z - campanatoConstant P u x (2 * r)| ∂P.μ) + _ at hcmp
  change (∫ z in ball x (2 * r), |u z - campanatoConstant P u x (2 * r)| ∂P.μ) ≤ _ at hbx
  change (∫ z in ball y (2 * r), |u z - campanatoConstant P u y (2 * r)| ∂P.μ) ≤ _ at hby
  dsimp only [Pi.sub_apply] at hmon
  unfold integralOscillation at hcmp
  nlinarith
end RothschildStein.H2
