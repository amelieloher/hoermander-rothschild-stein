-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Semigroup.ScalarMultipliers

/-! # Scalar estimates for the heat generator

A quadratic bound for the negative exponential controls the difference quotient after
multiplication by the resolvent coordinate. The unweighted error remains bounded by one.
-/

@[expose] public section
noncomputable section
namespace HeatKernel

theorem exp_neg_sub_one_add_mem_Icc {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-x) - 1 + x ∈ Set.Icc (0 : ℝ) (x ^ 2) := by
  have hlo := Real.add_one_le_exp (-x)
  have hexp : Real.exp (-x) ≤ (1 + x)⁻¹ := by
    rw [Real.exp_neg]
    apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
    simpa [add_comm] using Real.add_one_le_exp x
  have hpoly : (1 + x)⁻¹ ≤ 1 - x + x ^ 2 := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ (show 0 < 1 + x by positivity)).mpr
    nlinarith [mul_nonneg hx (sq_nonneg x)]
  exact ⟨by linarith, by linarith⟩

/-- Error in the generator difference quotient on the resolvent range. -/
def generatorMultiplierError (t r : ℝ) : ℝ :=
  r * (heatMultiplier t r - 1) / t - (r - 1)

theorem continuous_generatorMultiplierError (t : ℝ) :
    Continuous (generatorMultiplierError t) := by
  unfold generatorMultiplierError
  exact ((continuous_id.mul ((continuous_heatMultiplier t).sub continuous_const)).div_const t).sub
    (continuous_id.sub continuous_const)

theorem generatorMultiplierError_mem_Icc {t r : ℝ} (ht : 0 < t)
    (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    generatorMultiplierError t r ∈ Set.Icc (0 : ℝ) 1 := by
  rcases eq_or_lt_of_le hr.1 with hzero | hpos
  · rw [← hzero]
    simp [generatorMultiplierError]
  have hx : 0 ≤ t * (r⁻¹ - 1) := by
    have hinv : 1 ≤ r⁻¹ := (one_le_inv₀ hpos).mpr hr.2
    positivity
  have he := (exp_neg_sub_one_add_mem_Icc hx).1
  have hid : generatorMultiplierError t r =
      r / t * (Real.exp (-(t * (r⁻¹ - 1))) - 1 + t * (r⁻¹ - 1)) := by
    unfold generatorMultiplierError
    rw [heatMultiplier_of_pos ht hpos]
    field_simp
    ring
  constructor
  · rw [hid]
    exact mul_nonneg (div_nonneg hr.1 ht.le) he
  · unfold generatorMultiplierError
    have hneg : r * (heatMultiplier t r - 1) / t ≤ 0 := by
      exact div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos hr.1 (sub_nonpos.mpr (heatMultiplier_le_one ht hr))) ht.le
    linarith

theorem weighted_generatorMultiplierError_le {t r : ℝ} (ht : 0 < t)
    (hr : r ∈ Set.Icc (0 : ℝ) 1) : r * generatorMultiplierError t r ≤ t := by
  rcases eq_or_lt_of_le hr.1 with hzero | hpos
  · rw [← hzero]; simpa using ht.le
  have hinv : 1 ≤ r⁻¹ := (one_le_inv₀ hpos).mpr hr.2
  have hx : 0 ≤ t * (r⁻¹ - 1) := mul_nonneg ht.le (sub_nonneg.mpr hinv)
  have he := (exp_neg_sub_one_add_mem_Icc hx).2
  have hid : r * generatorMultiplierError t r =
      r ^ 2 / t * (Real.exp (-(t * (r⁻¹ - 1))) - 1 + t * (r⁻¹ - 1)) := by
    unfold generatorMultiplierError
    rw [heatMultiplier_of_pos ht hpos]
    field_simp
    ring
  rw [hid]
  calc
    _ ≤ r ^ 2 / t * (t * (r⁻¹ - 1)) ^ 2 :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = t * (1 - r) ^ 2 := by field_simp
    _ ≤ t := by nlinarith [mul_nonneg (sub_nonneg.mpr hr.2) hr.1]

end HeatKernel
