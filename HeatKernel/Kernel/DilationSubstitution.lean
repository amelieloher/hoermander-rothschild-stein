-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.DilationLimit
public import RothschildStein.G2.DilationMeasure
public import RothschildStein.G2.Measure

/-! # Initial condition from translation and dilation covariance

Haar substitution turns a covariant kernel row into a dilated time-one profile.
An integrable profile of mass one then gives the pointwise initial condition.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace HeatKernel

open RothschildStein RothschildStein.G2

/-- Translation and parabolic covariance give the exact time-one profile substitution. -/
theorem integral_kernel_eq_dilated_profile {n : ℕ} (G : HomogeneousGroup n)
    (p : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ)
    (hinv : ∀ t, 0 < t → ∀ g x y, p t (G.mul g x) (G.mul g y) = p t x y)
    (hscale : ∀ r t, 0 < r → 0 < t → ∀ x y,
      p (r ^ 2 * t) (G.dilate r x) (G.dilate r y) =
        (r ^ G.homogeneousDimension)⁻¹ * p t x y)
    (φ : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) {r : ℝ} (hr : 0 < r) :
    (∫ y, p (r ^ 2) x y * φ y) =
      ∫ z, p 1 0 z * φ (G.mul x (G.dilate r z)) := by
  have hpoint (z : Fin n → ℝ) :
      p (r ^ 2) x (G.mul x (G.dilate r z)) =
        (r ^ G.homogeneousDimension)⁻¹ * p 1 0 z := by
    have hi := hinv (r ^ 2) (sq_pos_of_pos hr) x 0 (G.dilate r z)
    rw [mul_zero] at hi
    rw [hi]
    simpa only [mul_one, dilate_zero] using hscale r 1 hr zero_lt_one 0 z
  have hd := integral_dilate G hr
    (fun y => p (r ^ 2) x (G.mul x y) * φ (G.mul x y))
  have hl := integral_leftTranslation G x (fun y => p (r ^ 2) x y * φ y)
  have heq : (∫ z, p (r ^ 2) x (G.mul x (G.dilate r z)) *
      φ (G.mul x (G.dilate r z))) =
      (r ^ G.homogeneousDimension)⁻¹ *
        ∫ z, p 1 0 z * φ (G.mul x (G.dilate r z)) := by
    simp_rw [hpoint, _root_.mul_assoc]
    exact integral_const_mul _ _
  have hc : (r ^ G.homogeneousDimension)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ hr.ne')
  apply mul_left_cancel₀ hc
  have hd' : (r ^ G.homogeneousDimension)⁻¹ * (∫ y, p (r ^ 2) x y * φ y) =
      ∫ z, p (r ^ 2) x (G.mul x (G.dilate r z)) * φ (G.mul x (G.dilate r z)) := by
    rw [← hl]
    simpa only [smul_eq_mul] using hd.symm
  exact hd'.trans heq

/-- A covariant kernel with an integrable unit-mass profile has the pointwise initial condition. -/
theorem tendsto_kernel_integral_of_covariance_and_unit_mass {n : ℕ}
    (G : HomogeneousGroup n) (p : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ)
    (hinv : ∀ t, 0 < t → ∀ g x y, p t (G.mul g x) (G.mul g y) = p t x y)
    (hscale : ∀ r t, 0 < r → 0 < t → ∀ x y,
      p (r ^ 2 * t) (G.dilate r x) (G.dilate r y) =
        (r ^ G.homogeneousDimension)⁻¹ * p t x y)
    (hk : Integrable (p 1 0)) (hmass : ∫ z, p 1 0 z = 1)
    {φ : (Fin n → ℝ) → ℝ} (hφ : Continuous φ)
    {C : ℝ} (hC : ∀ z, ‖φ z‖ ≤ C) (x : Fin n → ℝ) :
    Tendsto (fun t => ∫ y, p t x y * φ y) (𝓝[>] 0) (𝓝 (φ x)) := by
  apply tendsto_kernel_integral_of_dilation G p hk hmass hφ hC x
  intro t ht
  simpa only [Real.sq_sqrt ht.le] using
    integral_kernel_eq_dilated_profile G p hinv hscale φ x (Real.sqrt_pos.mpr ht)

end HeatKernel
