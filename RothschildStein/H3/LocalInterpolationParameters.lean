-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.HoleFillingInterpolation
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3

/-- The actual cutoff scale lies in the compact interpolation
range, and its horizontal coefficient is at most the chosen parameter. -/
theorem local_interpolation_scale_bounds {η d R B a : ℝ}
    (hη : 0 < η) (hη4 : η ≤ 1 / 4) (hd : 0 < d) (hdR : d ≤ R)
    (hB1 : 1 ≤ B) (hBR : R ≤ B) (hBa : 2 * a ≤ B) :
    0 < η * d / B ∧ η * d / B < 1 ∧
      η * d / B ≤ η ∧ (η * d / B) * (2 * a / d) ≤ η := by
  have hB : 0 < B := by linarith
  have he : η * d / B ≤ η := (div_le_iff₀ hB).mpr
    (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hdR.trans hBR) hη.le)
  refine ⟨div_pos (mul_pos hη hd) hB, lt_of_le_of_lt he (by linarith), he, ?_⟩
  have hi : 2 * a / B ≤ 1 := (div_le_one hB).mpr hBa
  have heq : (η * d / B) * (2 * a / d) = η * (2 * a / B) := by
    field_simp [hB.ne', hd.ne']
  rw [heq]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hi hη.le

/-- Exact far-scale loss for the chosen interpolation scale. -/
theorem local_interpolation_scale_loss {η d B γ : ℝ}
    (hη : 0 < η) (hd : 0 < d) (hB : 0 < B) :
    (η * d / B) ^ (-γ) = B ^ γ * η ^ (-γ) * d ^ (-γ) := by
  rw [Real.div_rpow (mul_pos hη hd).le hB.le, Real.mul_rpow hη.le hd.le,
    Real.rpow_neg hB.le]
  simp only [div_inv_eq_mul]
  ring

/-- The weight-two lower-order term has the same loss as
compact interpolation when gamma is at least one and the gap is bounded. -/
theorem local_interpolation_lower_order_loss {η d R γ : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1) (hd : 0 < d) (hdR : d ≤ R)
    (hγ : 1 ≤ γ) :
    η / d ≤ R ^ (γ - 1) * η ^ (-γ) * d ^ (-γ) := by
  have hR : 0 < R := hd.trans_le hdR
  have hηpow : η ≤ η ^ (-γ) := hη1.trans
    (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hη hη1 (by linarith))
  have hdpow : d ^ (γ - 1) ≤ R ^ (γ - 1) :=
    Real.rpow_le_rpow hd.le hdR (by linarith)
  have heq : η / d = d ^ (γ - 1) * η * d ^ (-γ) := by
    rw [mul_right_comm (d ^ (γ - 1)) η, ← Real.rpow_add hd]
    rw [show γ - 1 + -γ = (-1 : ℝ) by ring, Real.rpow_neg_one]
    ring
  rw [heq]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul hdpow hηpow hη.le (Real.rpow_nonneg hR.le _))
    (Real.rpow_nonneg hd.le _)

end RothschildStein.H3
