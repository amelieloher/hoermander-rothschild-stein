-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Gaussian.TimeNormalization
public import HeatKernel.Gaussian.KernelIntegrals
public import HeatKernel.Gaussian.NearDiagonalContinuity
public import HeatKernel.Gaussian.NearDiagonalScaling

/-! # Gaussian lower bounds from a scaled positive seed

A positive lower bound on a fixed parabolic neighborhood gives a global Gaussian
lower bound by restricted convolution. The single-volume prefactor is converted
to the homogeneous time power using the fixed unit-ball volume.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric RothschildStein
namespace HeatKernel.Gaussian

/-- A positive time-power seed on any fixed parabolic neighborhood, together
with nonnegative integrable convolution, gives positive Gaussian lower constants. -/
theorem exists_gaussian_lower_bound_of_time_power_seed {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (p : ℝ → CarnotPoint G hq hqpos hspan → CarnotPoint G hq hqpos hspan → ℝ)
    {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c)
    (hn : ∀ t, 0 < t → ∀ x y, 0 ≤ p t x y)
    (hi : ∀ s t, 0 < s → 0 < t → ∀ x y,
      Integrable (fun z ↦ p s x z * p t z y) (CarnotPoint.volume G hq hqpos hspan))
    (hconv : ∀ s t, 0 < s → 0 < t → ∀ x y,
      p (s + t) x y = ∫ z, p s x z * p t z y ∂(CarnotPoint.volume G hq hqpos hspan))
    (hnear : ∀ t, 0 < t → ∀ x y, dist x y ≤ ε * Real.sqrt t →
      c * t ^ (-(G.homogeneousDimension : ℝ) / 2) ≤ p t x y) :
    ∃ b B : ℝ, 0 < b ∧ 0 < B ∧ ∀ t, 0 < t → ∀ x y,
      b * t ^ (-(G.homogeneousDimension : ℝ) / 2) *
        Real.exp (-B * (dist x y ^ 2 / t)) ≤ p t x y := by
  let v := volume.real (horizontalBall (G.horizontalFields hq) 0 1)
  have hv : 0 < v := horizontal_unit_ball_volume_real_pos G hq hqpos hspan hw
  let a := min 1 (4 * ε)
  have ha : 0 < a := lt_min zero_lt_one (by positivity)
  have ha1 : a ≤ 1 := min_le_left _ _
  have haε : a / 4 ≤ ε := (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr
    (by dsimp [a]; linarith [min_le_right (1 : ℝ) (4 * ε)])
  let b := min ((c * v) * (a / 32) ^ G.homogeneousDimension) (1 / 2)
  have hb : 0 < b := lt_min (mul_pos (mul_pos hc hv) (by positivity)) (by norm_num)
  have hb1 : b < 1 := (min_le_right _ _).trans_lt (by norm_num)
  let B := (64 / a ^ 2) * Real.log (1 / b)
  have hB : 0 < B := mul_pos (by positivity)
    (Real.log_pos ((lt_div_iff₀ hb).mpr (by simpa using hb1)))
  have hseed : ∀ s, 0 < s → ∀ z w, dist z w ≤ a * Real.sqrt s / 4 →
      ENNReal.ofReal ((c * v) / (CarnotPoint.volume G hq hqpos hspan).real
        (ball z (Real.sqrt s))) ≤ ENNReal.ofReal (p s z w) := by
    intro s hs z w hzw
    have hd : dist z w ≤ ε * Real.sqrt s := hzw.trans (by
      calc
        a * Real.sqrt s / 4 = (a / 4) * Real.sqrt s := by ring
        _ ≤ ε * Real.sqrt s := mul_le_mul_of_nonneg_right haε (Real.sqrt_nonneg s))
    have he := mul_time_power_eq_unit_volume_div_heat_volume G hq hqpos hspan hw c z hs
    exact ENNReal.ofReal_le_ofReal (he ▸ hnear s hs z w hd)
  refine ⟨b / v, B, div_pos hb hv, hB, ?_⟩
  intro t ht x y
  have hl := carnot_gaussian_lower_bound_of_near_diagonal G hq hqpos hspan hw
    (fun s z w ↦ ENNReal.ofReal (p s z w)) ha ha1 (mul_pos hc hv) hseed
    (fun s u hs hu z w ↦ lintegral_kernel_convolution_of_real
      (CarnotPoint.volume G hq hqpos hspan) p hn hi hconv hs hu z w) ht x y
  change ENNReal.ofReal (b * Real.exp (-B * (dist x y ^ 2 / t)) /
    (CarnotPoint.volume G hq hqpos hspan).real (ball x (Real.sqrt t))) ≤
      ENNReal.ofReal (p t x y) at hl
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hl
  rw [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (hn t ht x y)] at hr
  change (b * Real.exp (-B * (dist x y ^ 2 / t))) *
    ((CarnotPoint.volume G hq hqpos hspan).real (ball x (Real.sqrt t)))⁻¹ ≤ p t x y at hr
  rw [inv_carnot_heat_volume_eq G hq hqpos hspan hw x ht] at hr
  convert hr using 1
  dsimp [v]
  ring

/-- Continuity, a positive identity diagonal and homogeneous covariance give
Gaussian lower bounds once nonnegative integrable convolution is available. -/
theorem exists_gaussian_lower_bound_of_continuity_and_covariance {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (p : ℝ → (Fin N → ℝ) → (Fin N → ℝ) → ℝ)
    (hcont : Continuous (fun z : CarnotPoint G hq hqpos hspan ↦ p 1 0 z))
    (hpos : 0 < p 1 0 0)
    (hleft : ∀ t, 0 < t → ∀ a x y, p t (G.mul a x) (G.mul a y) = p t x y)
    (hscale : ∀ t r, 0 < t → 0 < r → ∀ x y,
      p (r ^ 2 * t) (G.dilate r x) (G.dilate r y) =
        (r ^ G.homogeneousDimension)⁻¹ * p t x y)
    (hn : ∀ t, 0 < t → ∀ x y, 0 ≤ p t x y)
    (hi : ∀ s t, 0 < s → 0 < t → ∀ x y : CarnotPoint G hq hqpos hspan,
      Integrable (fun z ↦ p s x z * p t z y) (CarnotPoint.volume G hq hqpos hspan))
    (hconv : ∀ s t, 0 < s → 0 < t → ∀ x y : CarnotPoint G hq hqpos hspan,
      p (s + t) x y = ∫ z, p s x z * p t z y ∂(CarnotPoint.volume G hq hqpos hspan)) :
    ∃ b B : ℝ, 0 < b ∧ 0 < B ∧ ∀ t, 0 < t →
      ∀ x y : CarnotPoint G hq hqpos hspan,
        b * t ^ (-(G.homogeneousDimension : ℝ) / 2) *
          Real.exp (-B * (dist x y ^ 2 / t)) ≤ p t x y := by
  obtain ⟨ε, hε, hunit⟩ := exists_unit_near_diagonal_radius_of_continuity
    G hq hqpos hspan (p 1) hcont hpos (hleft 1 zero_lt_one)
  apply exists_gaussian_lower_bound_of_time_power_seed G hq hqpos hspan hw
    (fun t x y ↦ p t x y) (c := p 1 0 0 / 2) hε
    (div_pos hpos (by norm_num)) hn hi hconv
  intro t ht x y hxy
  exact near_diagonal_lower_bound_of_unit_time G hq hqpos hspan hw p hscale hunit ht x y hxy

end HeatKernel.Gaussian
