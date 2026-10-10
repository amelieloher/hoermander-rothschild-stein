-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.LogarithmicEnergyAbsorption
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import HeatKernel.Moser.MeanValueLinearTailTests

/-! # Coefficient-form absorption of truncated-power cutoff flux

Positivity of the symmetric coefficient form controls the mixed pairing itself.
The two truncation regions retain the power cutoff weight and the quadratic
high-level tail, respectively.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace HeatKernel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A weighted principal coefficient absorbs a coefficient-form mixed term,
retaining half of the principal flux. -/
theorem caccioppoli_weighted_bilinear_absorption
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hsym : ∀ v w, B v w = B w v)
    (hpos : ∀ v, 0 ≤ B v v) {κ w : ℝ} (hκ : 0 < κ) (hw : 0 ≤ w)
    (s η : ℝ) (g d : E) :
    κ * w / 2 * η ^ 2 * B g g - (2 * w * s ^ 2 / κ) * B d d ≤
      κ * w * η ^ 2 * B g g + 2 * w * s * η * B g d := by
  have h := logarithmic_energy_absorption B hsym hpos (κ * η) g ((-s) • d)
  simp only [map_smul, smul_apply, smul_eq_mul] at h
  have hbase : κ / 2 * η ^ 2 * B g g - (2 * s ^ 2 / κ) * B d d ≤
      κ * η ^ 2 * B g g + 2 * s * η * B g d := by
    apply (mul_le_mul_iff_of_pos_left hκ).mp
    convert h using 1 <;> field_simp [hκ.ne']
    ring
  have hscaled := mul_le_mul_of_nonneg_left hbase hw
  convert hscaled using 1 <;> ring

/-- Below the truncation level, the matrix flux absorbs with the full power cutoff
weight and the reciprocal exponent coefficient. -/
theorem caccioppoli_bilinear_power_below
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hsym : ∀ v w, B v w = B w v)
    (hpos : ∀ v, 0 ≤ B v v) {M p s : ℝ}
    (hM : 0 < M) (hp : 2 ≤ p) (hs : 0 < s) (hsM : s < M)
    (η : ℝ) (g d : E) :
    linearTailPositivePowerSlope M (p - 1) s / 2 * η ^ 2 * B g g -
      (2 / (p - 1)) * s ^ p * B d d ≤
    linearTailPositivePowerSlope M (p - 1) s * η ^ 2 * B g g +
      2 * (linearTailPowerWeakSolutionTest hM (show 1 ≤ p - 1 by linarith)).toFun s *
        η * B g d := by
  have hweight : s ^ (p - 2) * s ^ 2 = s ^ p := by
    rw [← Real.rpow_natCast s 2, ← Real.rpow_add hs]
    congr 1
    ring
  have h := caccioppoli_weighted_bilinear_absorption B hsym hpos
    (by linarith : 0 < p - 1) (Real.rpow_nonneg hs.le (p - 2)) s η g d
  rw [linearTailPowerWeakSolutionTest_apply_power hM hp hs.le, min_eq_left hsM.le]
  simp only [linearTailPositivePowerSlope, ite_eq_left hs, ite_eq_left hsM,
    show p - 1 - 1 = p - 2 by ring]
  have he : 2 * s ^ (p - 2) * s ^ 2 / (p - 1) = (2 / (p - 1)) * s ^ p := by
    rw [← hweight]
    ring
  rw [he] at h
  convert h using 1
  ring

/-- Above the truncation level, matrix absorption leaves exactly the quadratic
high-level cutoff weight, suitable for the vanishing-tail argument. -/
theorem caccioppoli_bilinear_power_above
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hsym : ∀ v w, B v w = B w v)
    (hpos : ∀ v, 0 ≤ B v v) {M p s : ℝ}
    (hM : 0 < M) (hp : 2 ≤ p) (hMs : M ≤ s)
    (η : ℝ) (g d : E) :
    linearTailPositivePowerSlope M (p - 1) s / 2 * η ^ 2 * B g g -
      2 * (s ^ 2 * M ^ (p - 2)) * B d d ≤
    linearTailPositivePowerSlope M (p - 1) s * η ^ 2 * B g g +
      2 * (linearTailPowerWeakSolutionTest hM (show 1 ≤ p - 1 by linarith)).toFun s *
        η * B g d := by
  have hs : 0 < s := hM.trans_le hMs
  have h := caccioppoli_weighted_bilinear_absorption B hsym hpos zero_lt_one
    (Real.rpow_nonneg hM.le (p - 2)) s η g d
  rw [linearTailPowerWeakSolutionTest_apply_power hM hp hs.le, min_eq_right hMs]
  simp only [linearTailPositivePowerSlope, ite_eq_left hs, ite_eq_right (not_lt.mpr hMs),
    show p - 1 - 1 = p - 2 by ring]
  convert h using 1 <;> ring

end HeatKernel
