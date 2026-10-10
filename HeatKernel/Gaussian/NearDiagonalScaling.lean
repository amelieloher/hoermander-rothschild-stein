-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Gaussian.NearDiagonalContinuity
public import HeatKernel.Gaussian.NaturalKernelScaling
public import HeatKernel.Geometry.MetricCovariance

/-! # Scaling a near-diagonal lower seed to positive times

Parabolic covariance transports a fixed unit-time neighborhood to a neighborhood
whose radius is proportional to the square root of the heat time.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric RothschildStein
namespace HeatKernel.Gaussian
set_option backward.isDefEq.respectTransparency false

/-- A unit-time lower seed on a fixed horizontal neighborhood gives a uniform
lower bound on its parabolically scaled neighborhoods. -/
theorem near_diagonal_lower_bound_of_unit_time {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (p : ℝ → (Fin N → ℝ) → (Fin N → ℝ) → ℝ)
    (hscale : ∀ t r, 0 < t → 0 < r → ∀ x y,
      p (r ^ 2 * t) (G.dilate r x) (G.dilate r y) =
        (r ^ G.homogeneousDimension)⁻¹ * p t x y)
    {ε c : ℝ}
    (hunit : ∀ x y : CarnotPoint G hq hqpos hspan, dist x y ≤ ε → c ≤ p 1 x y)
    {t : ℝ} (ht : 0 < t) (x y : CarnotPoint G hq hqpos hspan)
    (hxy : dist x y ≤ ε * Real.sqrt t) :
    c * t ^ (-(G.homogeneousDimension : ℝ) / 2) ≤ p t x y := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  let a : CarnotPoint G hq hqpos hspan := G.dilate (Real.sqrt t)⁻¹ x
  let b : CarnotPoint G hq hqpos hspan := G.dilate (Real.sqrt t)⁻¹ y
  have hab : dist a b ≤ ε := by
    calc
      dist a b = (Real.sqrt t)⁻¹ * dist x y :=
        CarnotPoint.dist_dilate G hq hqpos hspan hw (inv_pos.mpr hs) x y
      _ ≤ (Real.sqrt t)⁻¹ * (ε * Real.sqrt t) :=
        mul_le_mul_of_nonneg_left hxy (inv_nonneg.mpr hs.le)
      _ = ε := by field_simp
  have hi : t ^ (-(1 : ℝ) / 2) = (Real.sqrt t)⁻¹ := by
    rw [neg_div, Real.rpow_neg ht.le, Real.sqrt_eq_rpow]
  have he := homogeneous_kernel_eq_unit_time_of_nat_covariance G p hscale ht x y
  rw [hi] at he
  calc
    _ = t ^ (-(G.homogeneousDimension : ℝ) / 2) * c := mul_comm _ _
    _ ≤ t ^ (-(G.homogeneousDimension : ℝ) / 2) * p 1 a b :=
      mul_le_mul_of_nonneg_left (hunit a b hab) (Real.rpow_pos_of_pos ht _).le
    _ = p t x y := he.symm

end HeatKernel.Gaussian
