-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Gaussian.CarnotLowerBound
public import HeatKernel.Gaussian.MeanValueIntegral
public import HeatKernel.Gaussian.EndpointBounds
import Mathlib.Tactic

/-! # Gaussian upper constants from endpoint mean-value estimates

Exact homogeneous volumes convert the two endpoint estimates to a squared
pointwise estimate. Taking its square root and absorbing the linear exponential
loss gives the explicit upper constants with decay exponent one twenty-fourth.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric RothschildStein
namespace HeatKernel.Gaussian

/-- The half heat radius has a center-independent volume ratio. -/
theorem carnot_volume_half_radius_eq {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N)
    (hqpos : 0 < q) (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (x y : CarnotPoint G hq hqpos hspan) {t : ℝ} (ht : 0 < t) :
    (CarnotPoint.volume G hq hqpos hspan).real (ball y (Real.sqrt t / 2)) =
      (CarnotPoint.volume G hq hqpos hspan).real (ball x (Real.sqrt t)) /
        (2 : ℝ) ^ G.homogeneousDimension := by
  rw [CarnotPoint.volumeReal_ball G hq hqpos hspan hw y (by positivity),
    CarnotPoint.volumeReal_ball G hq hqpos hspan hw x (Real.sqrt_pos.mpr ht), div_pow]
  ring

/-- The uniform first-row bound and the second endpoint mean-value estimate
imply the Gaussian upper estimate with explicit homogeneous constants. -/
theorem carnot_gaussian_upper_bound_of_endpoint_mean_values {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {t : ℝ} (ht : 0 < t) (x y : CarnotPoint G hq hqpos hspan)
    (value Cpm : ℝ) (f : ℝ → ℝ) :
    let r := Real.sqrt t / 4;
    let β := dist x y / (6 * t);
    IntegrableOn f (Ioo (t - 7 * r ^ 2 / 2) (t + r ^ 2 / 2)) →
    (∀ σ ∈ Ioo (t - 7 * r ^ 2 / 2) (t + r ^ 2 / 2),
      f σ ≤ 4 * Cpm ^ 2 / (CarnotPoint.volume G hq hqpos hspan).real (ball y (2 * r)) *
        Real.exp (-2 * β * dist x y + 8 * β * r + 6 * β ^ 2 * t)) →
    (value ^ 2 ≤ Cpm ^ 2 / (r ^ 2 *
      (CarnotPoint.volume G hq hqpos hspan).real (ball x (2 * r))) *
        ∫ σ in Ioo (t - 7 * r ^ 2 / 2) (t + r ^ 2 / 2), f σ) →
    value ≤ (4 * (2 : ℝ) ^ G.homogeneousDimension * Real.exp (1 / 6) * Cpm ^ 2 /
      (CarnotPoint.volume G hq hqpos hspan).real (ball x (Real.sqrt t))) *
        Real.exp (-(1 / 24 : ℝ) * (dist x y ^ 2 / t)) := by
  dsimp only
  intro hf hrow hmean
  let μ := CarnotPoint.volume G hq hqpos hspan
  let V := μ.real (ball x (Real.sqrt t))
  let M := 4 * (2 : ℝ) ^ G.homogeneousDimension * Cpm ^ 2
  have hV : 0 < V := by
    dsimp [V, μ]
    rw [CarnotPoint.volumeReal_ball G hq hqpos hspan hw x (Real.sqrt_pos.mpr ht)]
    exact mul_pos (horizontal_unit_ball_volume_real_pos G hq hqpos hspan hw)
      (pow_pos (Real.sqrt_pos.mpr ht) _)
  have htwo : 0 < (2 : ℝ) ^ G.homogeneousDimension := by positivity
  have h2r : 2 * (Real.sqrt t / 4) = Real.sqrt t / 2 := by ring
  have hX : 0 < μ.real (ball x (2 * (Real.sqrt t / 4))) := by
    rw [h2r, carnot_volume_half_radius_eq G hq hqpos hspan hw x x ht]
    exact div_pos hV htwo
  have hY : 0 < μ.real (ball y (2 * (Real.sqrt t / 4))) := by
    rw [h2r, carnot_volume_half_radius_eq G hq hqpos hspan hw x y ht]
    exact div_pos hV htwo
  have H := sq_le_of_two_endpoint_mean_values (by positivity : 0 < Real.sqrt t / 4)
    hX hY hf hrow hmean
  rw [h2r, carnot_volume_half_radius_eq G hq hqpos hspan hw x x ht,
    carnot_volume_half_radius_eq G hq hqpos hspan hw x y ht,
    endpoint_weight_exponent_eq ht (dist x y)] at H
  have hcoef : 16 * Cpm ^ 4 / (V / (2 : ℝ) ^ G.homogeneousDimension *
      (V / (2 : ℝ) ^ G.homogeneousDimension)) = (M / V) ^ 2 := by
    dsimp [M]
    field_simp
    ring
  change value ^ 2 ≤ (16 * Cpm ^ 4 /
    (V / (2 : ℝ) ^ G.homogeneousDimension * (V / (2 : ℝ) ^ G.homogeneousDimension))) *
      Real.exp (-(dist x y / Real.sqrt t) ^ 2 / 6 + (dist x y / Real.sqrt t) / 3) at H
  rw [hcoef] at H
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hb := le_gaussian_of_squared_endpoint_bound hM hV H
  rw [sq_div_sqrt ht.le] at hb
  calc
    value ≤ (M * Real.exp (1 / 6) / V) * Real.exp (-(dist x y ^ 2 / t) / 24) := hb
    _ = _ := by
      dsimp [M, V, μ]
      congr 1
      · ring
      · congr 1
        ring

end HeatKernel.Gaussian
