-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.VolumeGrowth
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- A single annulus needs one doubling, even when the outer shell is
truncated. BB Lemma 7.5, p. 297. -/
theorem DoublingPatch.weighted_annulus (P : DoublingPatch X) {z : X} (hz : z ∈ P.S)
    {a b : ℝ} (ha : 0 < a) (hb : b ≤ 6 * P.ρ) (hba : b ≤ 2 * a)
    (f : X → ℝ≥0∞) (w : ℝ≥0∞) (hw : ∀ y, a ≤ dist z y → dist z y < b → f y ≤ w) :
    (∫⁻ y in {y | a ≤ dist z y ∧ dist z y < b},
      f y * (volumeAt P.μ z y)⁻¹ ∂P.μ) ≤ w * ENNReal.ofReal P.C_D := by
  by_cases hab : a < b
  · have hv := P.doubling z hz a ha (hab.le.trans hb)
    have hd := (P.doubling z hz b (ha.trans hab) hb).2.2
    have hd' : P.μ (ball z b) ≤ ENNReal.ofReal P.C_D * P.μ (ball z a) :=
      hd.trans (mul_le_mul_right (measure_mono (ball_subset_ball (by linarith : b / 2 ≤ a))) _)
    calc
      _ ≤ ∫⁻ _y in {y | a ≤ dist z y ∧ dist z y < b}, w * (P.μ (ball z a))⁻¹ ∂P.μ := by
        apply setLIntegral_mono measurable_const
        intro y hy
        have hi : (volumeAt P.μ z y)⁻¹ ≤ (P.μ (ball z a))⁻¹ :=
          ENNReal.inv_le_inv.mpr (measure_mono (ball_subset_ball (x := z) hy.1))
        exact (mul_le_mul_left (hw y hy.1 hy.2) _).trans (mul_le_mul_right hi _)
      _ = (w * (P.μ (ball z a))⁻¹) * P.μ {y | a ≤ dist z y ∧ dist z y < b} :=
        setLIntegral_const _ _
      _ ≤ (w * (P.μ (ball z a))⁻¹) * P.μ (ball z b) :=
        mul_le_mul_right (measure_mono (show {y : X | a ≤ dist z y ∧ dist z y < b} ⊆ ball z b from
          fun y hy => by simpa [mem_ball, dist_comm] using hy.2)) _
      _ ≤ (w * (P.μ (ball z a))⁻¹) * (ENNReal.ofReal P.C_D * P.μ (ball z a)) :=
        mul_le_mul_right hd' _
      _ = w * ENNReal.ofReal P.C_D := by
        rw [mul_assoc, mul_left_comm (P.μ (ball z a))⁻¹,
          ENNReal.inv_mul_cancel (ne_of_gt hv.1) (ne_of_lt hv.2.1), mul_one]
  · have he : {y : X | a ≤ dist z y ∧ dist z y < b} = ∅ := by
      ext y; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]; intro hy; linarith
    rw [he, setLIntegral_empty]
    positivity

/-- Dyadic inner-shell coverage with a closed lower and open upper boundary. -/
theorem exists_inner_dyadic {r d : ℝ} (hd : 0 < d) (hdr : d < r) :
    ∃ n : ℕ, r / 2 ^ (n + 1) ≤ d ∧ d < r / 2 ^ n := by
  have hr := hd.trans hdr
  have hratio : 1 < r / d := (lt_div_iff₀ hd).mpr (by simpa using hdr)
  have hl : 0 < Real.logb 2 (r / d) := Real.logb_pos (by norm_num) hratio
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (Nat.ceil_pos.mpr hl))
  have htop : Real.logb 2 (r / d) ≤ (n + 1 : ℕ) := by
    simpa [hn] using (Nat.le_ceil (Real.logb 2 (r / d)))
  have hbot : (n : ℝ) < Real.logb 2 (r / d) := by
    by_contra h
    have hc : ⌈Real.logb 2 (r / d)⌉₊ ≤ n := Nat.ceil_le.mpr (le_of_not_gt h)
    omega
  have ht := (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) (div_pos hr hd)).mp htop
  have hb := (Real.lt_logb_iff_rpow_lt (by norm_num : (1 : ℝ) < 2) (div_pos hr hd)).mp hbot
  rw [Real.rpow_natCast] at ht hb
  refine ⟨n, ?_, ?_⟩
  · apply (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ (n + 1))).mpr
    have := (div_le_iff₀ hd).mp ht
    nlinarith
  · apply (lt_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ n)).mpr
    have := (lt_div_iff₀ hd).mp hb
    nlinarith

end RothschildStein.H2
