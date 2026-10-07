-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Abs
public import Mathlib.Analysis.Calculus.Deriv.Pi

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped Topology

namespace RothschildStein.G1

/-- Independent weighted root powers of absolute time
(BB Thm 1.48, pp. 32–34). -/
def weightedAbsolutePowers {n : ℕ} (α : Fin n → ℝ) (h : ℝ) : Fin n → ℝ :=
  fun i => |h| ^ α i

/-- The continuous normalized derivative hτ'(h) of weighted root
powers (BB Thm 1.48, pp. 32–34). -/
def weightedPowerRate {n : ℕ} (α : Fin n → ℝ) (h : ℝ) : Fin n → ℝ :=
  fun i => α i * |h| ^ α i

/-- Actual derivatives away from zero, with arbitrary value at zero
(BB Thm 1.48, pp. 32–34). -/
def weightedPowerDerivative {n : ℕ} (α : Fin n → ℝ) (h : ℝ) : Fin n → ℝ :=
  fun i => (α i * |h| ^ α i) / h

/-- Positive weighted root powers are jointly continuous in time
(BB Thm 1.48, pp. 32–34). -/
theorem weightedAbsolutePowers_continuous {n : ℕ} (α : Fin n → ℝ) (hα : ∀ i, 0 < α i) :
    Continuous (weightedAbsolutePowers α) := by
  apply continuous_pi
  intro i
  exact continuous_abs.rpow_const (fun _ => Or.inr (hα i).le)

/-- The normalized root derivative extends continuously to zero
(BB Thm 1.48, pp. 32–34). -/
theorem weightedPowerRate_continuous {n : ℕ} (α : Fin n → ℝ) (hα : ∀ i, 0 < α i) :
    Continuous (weightedPowerRate α) := by
  apply continuous_pi
  intro i
  exact continuous_const.mul (continuous_abs.rpow_const (fun _ => Or.inr (hα i).le))

/-- Root powers vanish at zero (BB Thm 1.48, pp. 32–34). -/
theorem weightedAbsolutePowers_zero {n : ℕ} (α : Fin n → ℝ) (hα : ∀ i, 0 < α i) :
    weightedAbsolutePowers α 0 = 0 := by
  funext i
  simp [weightedAbsolutePowers, Real.zero_rpow (hα i).ne']

/-- Normalized root derivatives vanish at zero (BB pp. 32–34). -/
theorem weightedPowerRate_zero {n : ℕ} (α : Fin n → ℝ) (hα : ∀ i, 0 < α i) :
    weightedPowerRate α 0 = 0 := by
  funext i
  simp [weightedPowerRate, Real.zero_rpow (hα i).ne']

/-- Each absolute-power derivative is computed only away from zero
(BB Thm 1.48, pp. 32–34). -/
theorem absolutePower_hasDerivAt {a h : ℝ} (hh : h ≠ 0) :
    HasDerivAt (fun t : ℝ => |t| ^ a) ((a * |h| ^ a) / h) h := by
  by_cases hp : 0 < h
  · have hd := (hasDerivAt_abs_pos hp).rpow_const (p := a) (Or.inl (abs_ne_zero.mpr hh))
    have he : 1 * a * |h| ^ (a - 1) = (a * |h| ^ a) / h := by
      rw [Real.rpow_sub_one (abs_ne_zero.mpr hh), abs_of_pos hp]
      ring
    simpa only [he] using hd
  · have hn : h < 0 := lt_of_le_of_ne (le_of_not_gt hp) hh
    have hd := (hasDerivAt_abs_neg hn).rpow_const (p := a) (Or.inl (abs_ne_zero.mpr hh))
    have he : -1 * a * |h| ^ (a - 1) = (a * |h| ^ a) / h := by
      rw [Real.rpow_sub_one (abs_ne_zero.mpr hh), abs_of_neg hn]
      field_simp
    simpa only [he] using hd

/-- The complete finite parameter vector has its actual derivative
away from zero (BB Thm 1.48, pp. 32–34). -/
theorem weightedAbsolutePowers_hasDerivAt {n : ℕ} (α : Fin n → ℝ)
    {h : ℝ} (hh : h ≠ 0) :
    HasDerivAt (weightedAbsolutePowers α) (weightedPowerDerivative α h) h := by
  have hd : HasFDerivAt (fun t : ℝ => fun i : Fin n => |t| ^ α i)
      (ContinuousLinearMap.pi (fun i : Fin n =>
        ContinuousLinearMap.toSpanSingleton ℝ ((α i * |h| ^ α i) / h))) h :=
    hasFDerivAt_pi.mpr (fun i => (absolutePower_hasDerivAt (a := α i) hh).hasFDerivAt)
  have he : (ContinuousLinearMap.pi (fun i : Fin n =>
      ContinuousLinearMap.toSpanSingleton ℝ ((α i * |h| ^ α i) / h))) 1 =
      weightedPowerDerivative α h := by
    funext i
    change (1 : ℝ) • ((α i * |h| ^ α i) / h) = (α i * |h| ^ α i) / h
    exact one_smul ℝ _
  change HasDerivAt (fun t : ℝ => fun i : Fin n => |t| ^ α i)
    (weightedPowerDerivative α h) h
  simpa only [he] using hd.hasDerivAt

/-- hτ'(h) equals the continuous normalized rate exactly
(BB Thm 1.48, pp. 32–34). -/
theorem weightedPowerDerivative_normalized {n : ℕ} (α : Fin n → ℝ)
    {h : ℝ} (hh : h ≠ 0) :
    h • weightedPowerDerivative α h = weightedPowerRate α h := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, weightedPowerDerivative, weightedPowerRate]
  exact mul_div_cancel₀ _ hh

end RothschildStein.G1
