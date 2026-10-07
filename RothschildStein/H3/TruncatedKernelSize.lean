-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.SphereMaximum

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.H3
variable {N : ℕ} {G : HomogeneousGroup N}

/-- size. Cutting a homogeneous kernel off at radius R changes
its type α size bound to any ν≤α, with precisely the factor R^{α−ν}.
This includes α=ν=0 and uses the actual sphere maximum (BB p. 350). -/
theorem truncatedHomogeneousKernel_size
    {ν T χ : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (hT : ContinuousOn T {0}ᶜ) {α v : ℝ}
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 →
      T (G.dilate t x) = t ^ (α - (G.homogeneousDimension : ℝ)) * T x)
    (hv : v ≤ α) {R : ℝ} (hR : 0 < R)
    (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (hsupp : ∀ x, R < ν x → χ x = 0) (x : Fin N → ℝ) (hx : x ≠ 0) :
    |χ x * T x| ≤ kernelSphereBound ν T * R ^ (α - v) *
      (ν x) ^ (v - (G.homogeneousDimension : ℝ)) := by
  have hΛ : 0 ≤ kernelSphereBound ν T := (kernelSphereBound_continuous hν hT).1
  have hp := G2.gauge_pos hν hx
  by_cases he : χ x = 0
  · rw [he, zero_mul, abs_zero]
    exact mul_nonneg (mul_nonneg hΛ (Real.rpow_nonneg hR.le _))
      (Real.rpow_nonneg hp.le _)
  have hbR : ν x ≤ R := le_of_not_gt (fun h => he (hsupp x h))
  have hb := kernelSphereBound_homogeneous hν hT hhom x hx
  have hsplit : (ν x) ^ (α - (G.homogeneousDimension : ℝ)) =
      (ν x) ^ (α - v) * (ν x) ^ (v - (G.homogeneousDimension : ℝ)) := by
    rw [← Real.rpow_add hp]
    congr 1
    ring
  calc
    |χ x * T x| = χ x * |T x| := by rw [abs_mul, abs_of_nonneg (hχ x).1]
    _ ≤ 1 * |T x| := mul_le_mul_of_nonneg_right (hχ x).2 (abs_nonneg _)
    _ ≤ kernelSphereBound ν T * (ν x) ^ (α - (G.homogeneousDimension : ℝ)) := by
      simpa only [one_mul] using hb
    _ = kernelSphereBound ν T * (ν x) ^ (α - v) *
        (ν x) ^ (v - (G.homogeneousDimension : ℝ)) := by rw [hsplit, mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hp.le hbR (sub_nonneg.mpr hv)) hΛ)
      (Real.rpow_nonneg hp.le _)

end RothschildStein.H3
