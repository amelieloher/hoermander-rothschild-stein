-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Semigroup.ScalarMultipliers
public import Mathlib.Basic.NNReal.Basic

/-! # Heat multipliers including time zero

The multiplier at time zero is the constant one. Multiplication by the resolvent coordinate
restores a uniform Lipschitz estimate in time, including at zero.
-/

@[expose] public section
noncomputable section

open scoped NNReal

namespace HeatKernel

/-- The heat multiplier for nonnegative time, with the identity multiplier at time zero. -/
def semigroupMultiplier (t : ℝ≥0) (r : ℝ) : ℝ :=
  if t = 0 then 1 else heatMultiplier t r

@[simp] theorem semigroupMultiplier_zero (r : ℝ) : semigroupMultiplier 0 r = 1 := by
  simp [semigroupMultiplier]

theorem semigroupMultiplier_of_pos {t : ℝ≥0} (ht : 0 < t) (r : ℝ) :
    semigroupMultiplier t r = heatMultiplier t r := by
  simp [semigroupMultiplier, ht.ne']

theorem continuous_semigroupMultiplier (t : ℝ≥0) : Continuous (semigroupMultiplier t) := by
  by_cases ht : t = 0
  · subst t
    have h : semigroupMultiplier 0 = (fun _ : ℝ => (1 : ℝ)) := funext semigroupMultiplier_zero
    rw [h]
    exact continuous_const
  · convert continuous_heatMultiplier (t : ℝ) using 1
    ext r
    exact semigroupMultiplier_of_pos (pos_iff_ne_zero.mpr ht) r

theorem semigroupMultiplier_add (s t : ℝ≥0) (r : ℝ) :
    semigroupMultiplier (s + t) r = semigroupMultiplier s r * semigroupMultiplier t r := by
  by_cases hs : s = 0
  · subst s; simp
  by_cases ht : t = 0
  · subst t; simp
  have hs' : 0 < s := pos_iff_ne_zero.mpr hs
  have ht' : 0 < t := pos_iff_ne_zero.mpr ht
  simp only [semigroupMultiplier_of_pos hs', semigroupMultiplier_of_pos ht',
    semigroupMultiplier_of_pos (add_pos hs' ht'), NNReal.coe_add]
  exact heatMultiplier_add hs' ht' r

theorem semigroupMultiplier_mem_Icc (t : ℝ≥0) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    semigroupMultiplier t r ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases ht : t = 0
  · subst t; simp
  rw [semigroupMultiplier_of_pos (pos_iff_ne_zero.mpr ht)]
  exact ⟨heatMultiplier_nonneg _ _, heatMultiplier_le_one (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr ht)) hr⟩

theorem weighted_semigroupMultiplier_sub_one_le (t : ℝ≥0) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) 1) : r * |semigroupMultiplier t r - 1| ≤ t := by
  by_cases ht : t = 0
  · subst t; simp
  rcases eq_or_lt_of_le hr.1 with hrzero | hrpos
  · rw [← hrzero]; simp
  have ht' : 0 < (t : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr ht)
  have hupper := (semigroupMultiplier_mem_Icc t hr).2
  have hexp := Real.add_one_le_exp (- (t : ℝ) * (r⁻¹ - 1))
  rw [semigroupMultiplier_of_pos (pos_iff_ne_zero.mpr ht), heatMultiplier_of_pos ht' hrpos] at *
  calc
    r * |Real.exp (-(t : ℝ) * (r⁻¹ - 1)) - 1| =
        r * (1 - Real.exp (-(t : ℝ) * (r⁻¹ - 1))) := by
      rw [abs_of_nonpos (sub_nonpos.mpr hupper)]; ring
    _ ≤ r * ((t : ℝ) * (r⁻¹ - 1)) := mul_le_mul_of_nonneg_left (by linarith) hr.1
    _ = (t : ℝ) * (1 - r) := by field_simp
    _ ≤ t := by nlinarith

private theorem weighted_semigroupMultiplier_sub_le_of_le {s t : ℝ≥0} (hst : s ≤ t)
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    r * |semigroupMultiplier t r - semigroupMultiplier s r| ≤ (t : ℝ) - s := by
  have hsum : t - s + s = t := tsub_add_cancel_of_le hst
  have hm : semigroupMultiplier t r =
      semigroupMultiplier (t - s) r * semigroupMultiplier s r := by
    simpa only [hsum] using semigroupMultiplier_add (t - s) s r
  have hs := semigroupMultiplier_mem_Icc s hr
  have hd := semigroupMultiplier_mem_Icc (t - s) hr
  have hw := weighted_semigroupMultiplier_sub_one_le (t - s) hr
  rw [abs_of_nonpos (sub_nonpos.mpr hd.2)] at hw
  have hdiff : semigroupMultiplier t r - semigroupMultiplier s r ≤ 0 := by
    rw [hm]; nlinarith [hs.1, hd.2]
  rw [abs_of_nonpos hdiff, hm]
  calc
    r * -(semigroupMultiplier (t - s) r * semigroupMultiplier s r -
        semigroupMultiplier s r) =
        (r * (1 - semigroupMultiplier (t - s) r)) * semigroupMultiplier s r := by ring
    _ ≤ r * (1 - semigroupMultiplier (t - s) r) := by
      exact mul_le_of_le_one_right (mul_nonneg hr.1 (sub_nonneg.mpr hd.2)) hs.2
    _ ≤ ((t - s : ℝ≥0) : ℝ) := by simpa using hw
    _ = (t : ℝ) - s := NNReal.coe_sub hst

theorem weighted_semigroupMultiplier_sub_le (s t : ℝ≥0) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    r * |semigroupMultiplier t r - semigroupMultiplier s r| ≤ dist t s := by
  rcases le_total s t with hst | hts
  · simpa [NNReal.dist_eq, abs_of_nonneg (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hst))]
      using weighted_semigroupMultiplier_sub_le_of_le hst hr
  · rw [abs_sub_comm]
    simpa [NNReal.dist_eq, abs_of_nonpos (sub_nonpos.mpr (NNReal.coe_le_coe.mpr hts))]
      using weighted_semigroupMultiplier_sub_le_of_le hts hr

end HeatKernel
