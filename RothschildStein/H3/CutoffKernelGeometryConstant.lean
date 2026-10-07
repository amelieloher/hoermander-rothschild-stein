-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.CutoffKernelDifference

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
variable {N q : ℕ}

/-- A single frame-and-dimension constant controls every degree in [-Q,0]. -/
def cutoffKernelFrameConstant (ν : (Fin N → ℝ) → ℝ)
    (Y : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)) (Q : ℝ) : ℝ :=
  (2 : ℝ) ^ (Q + 2) * max 0 (frameCoefficientSphereBound ν Y) +
    (2 : ℝ) ^ (Q + 1) + 4 * (1 + (2 : ℝ) ^ Q)

/-- The frame constant is strictly positive and has no scalar-kernel dependence. -/
theorem cutoffKernelFrameConstant_pos (ν : (Fin N → ℝ) → ℝ)
    (Y : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)) (Q : ℝ) :
    0 < cutoffKernelFrameConstant ν Y Q := by
  unfold cutoffKernelFrameConstant
  positivity

/-- Uniformity over the homogeneous-degree range leaves exactly the cutoff
factor 1 + R L, where L is the cutoff Lipschitz constant. -/
theorem cutoffKernelSmoothConstant_le_frame (ν : (Fin N → ℝ) → ℝ)
    (Y : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    {Q γ R L : ℝ} (hγ : -Q ≤ γ) (hR : 0 ≤ R) (hL : 0 ≤ L) :
    cutoffKernelSmoothConstant ν Y γ R L ≤
      cutoffKernelFrameConstant ν Y Q * (1 + R * L) := by
  have hfirst : (2 : ℝ) ^ (2 - γ) ≤ (2 : ℝ) ^ (Q + 2) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hsecond : (2 : ℝ) ^ (-γ) ≤ (2 : ℝ) ^ Q :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hmax : 0 ≤ max 0 (frameCoefficientSphereBound ν Y) := le_max_left _ _
  have hRL : 0 ≤ R * L := mul_nonneg hR hL
  have hp : (2 : ℝ) ^ (Q + 1) = (2 : ℝ) ^ Q * 2 := by
    rw [Real.rpow_add (by norm_num), Real.rpow_one]
  have hu : cutoffKernelSmoothConstant ν Y γ R L ≤
      (2 : ℝ) ^ (Q + 2) * max 0 (frameCoefficientSphereBound ν Y) +
        (2 : ℝ) ^ Q * (2 * R * L) + 4 * (1 + (2 : ℝ) ^ Q) := by
    unfold cutoffKernelSmoothConstant
    exact add_le_add (add_le_add (mul_le_mul_of_nonneg_right hfirst hmax)
      (mul_le_mul_of_nonneg_right hsecond (by positivity)))
      (mul_le_mul_of_nonneg_left (add_le_add_right hsecond 1) (by norm_num))
  apply hu.trans
  unfold cutoffKernelFrameConstant
  rw [hp]
  have hA : 0 ≤ (2 : ℝ) ^ (Q + 2) * max 0 (frameCoefficientSphereBound ν Y) :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) hmax
  have hB : 0 ≤ (2 : ℝ) ^ Q := Real.rpow_nonneg (by norm_num) _
  have hD : 0 ≤ 4 * (1 + (2 : ℝ) ^ Q) := by positivity
  nlinarith [mul_nonneg hA hRL, mul_nonneg hD hRL]

end RothschildStein.H3
