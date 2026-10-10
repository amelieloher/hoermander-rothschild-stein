-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MomentSplitting
public import HeatKernel.Moser.ReverseHolderIteration

/-!
# Exponential moment bounds from logarithmic tails

The small moment is split at the exponential of half the logarithmic larger
norm. Hölder's inequality and the logarithmic tail estimate give the moment
bound used in the finite-exponent argument of Bombieri and Giusti.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace HeatKernel

/-- Exponential upper tails and a larger moment bound control the small moment. -/
theorem lintegral_small_moment_le_two_exp {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ≥0∞} (hf : Measurable f)
    {U : Set α} (hμU : μ U ≤ 1) {p p₀ h a : ℝ}
    (hp : 0 < p) (hp₀ : 0 < p₀) (hpp₀ : p ≤ p₀ / 2)
    (ha : 0 ≤ a) (hph : p * h = a)
    (hmoment : (∫⁻ x in U, f x ^ p₀ ∂μ) ≤ ENNReal.ofReal (Real.exp (p₀ * h)))
    (htail : μ (U ∩ {x | ENNReal.ofReal (Real.exp (h / 2)) < f x}) ≤
      ENNReal.ofReal (Real.exp (-a))) :
    (∫⁻ x in U, f x ^ p ∂μ) ≤ ENNReal.ofReal (2 * Real.exp (a / 2)) := by
  have hp_lt : p < p₀ := by linarith
  have he : 1 / 2 ≤ 1 - p / p₀ := by
    have hh' : p / p₀ ≤ (1 / 2 : ℝ) := (div_le_iff₀ hp₀).2 (by linarith)
    linarith
  have hratio : 0 ≤ p / p₀ := div_nonneg hp.le hp₀.le
  have hsplit := lintegral_rpow_le_level_add_tail (μ := μ) hf hp hp_lt
    (U := U) (ENNReal.ofReal (Real.exp (h / 2)))
  have hlow : ENNReal.ofReal (Real.exp (h / 2)) ^ p * μ U ≤
      ENNReal.ofReal (Real.exp (a / 2)) := by
    calc
      _ ≤ ENNReal.ofReal (Real.exp (h / 2)) ^ p * 1 := mul_le_mul_right hμU _
      _ = _ := by
        rw [mul_one, ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul]
        congr 2
        nlinarith [hph]
  have hhigh : (∫⁻ x in U, f x ^ p₀ ∂μ) ^ (p / p₀) *
      μ (U ∩ {x | ENNReal.ofReal (Real.exp (h / 2)) < f x}) ^ (1 - p / p₀) ≤
      ENNReal.ofReal (Real.exp (a / 2)) := by
    calc
      _ ≤ ENNReal.ofReal (Real.exp (p₀ * h)) ^ (p / p₀) *
          ENNReal.ofReal (Real.exp (-a)) ^ (1 - p / p₀) :=
        mul_le_mul' (ENNReal.rpow_le_rpow hmoment hratio)
          (ENNReal.rpow_le_rpow htail (by linarith))
      _ = ENNReal.ofReal (Real.exp a * Real.exp (-a * (1 - p / p₀))) := by
        rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _),
          ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul, ← Real.exp_mul,
          ← ENNReal.ofReal_mul (Real.exp_pos _).le]
        congr 2
        congr 1
        field_simp
        nlinarith [hph]
      _ ≤ ENNReal.ofReal (Real.exp a * Real.exp (-a / 2)) := by
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        apply Real.exp_le_exp.mpr
        nlinarith
      _ = _ := by rw [← Real.exp_add]; congr 2; ring
  calc
    _ ≤ ENNReal.ofReal (Real.exp (a / 2)) + ENNReal.ofReal (Real.exp (a / 2)) :=
      hsplit.trans (add_le_add hlow hhigh)
    _ = _ := by rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]; congr 1; ring

/-- The logarithmic tail threshold gives the exponentially small level-set measure. -/
theorem div_le_exp_neg_of_logarithmic_threshold {A h a : ℝ}
    (hh : 0 < h) (hthreshold : 2 * A * Real.exp a ≤ h) :
    2 * A / h ≤ Real.exp (-a) := by
  apply (div_le_iff₀ hh).2
  have ht := mul_le_mul_of_nonneg_right hthreshold (Real.exp_pos (-a)).le
  have he : Real.exp a * Real.exp (-a) = 1 := by rw [← Real.exp_add]; simp
  have he' : 2 * A * Real.exp a * Real.exp (-a) = 2 * A := by
    calc
      _ = 2 * A * (Real.exp a * Real.exp (-a)) := by ring
      _ = _ := by rw [he]; ring
  rw [he'] at ht
  linarith

/-- Taking the logarithm of the small-moment bound yields the two-piece logarithmic estimate. -/
theorem log_toReal_le_half_add_log_two {I : ℝ≥0∞} {a : ℝ} (ha : 0 ≤ a)
    (hI : I ≤ ENNReal.ofReal (2 * Real.exp (a / 2))) :
    Real.log I.toReal ≤ a / 2 + Real.log 2 := by
  have hi : I.toReal ≤ 2 * Real.exp (a / 2) := by
    simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * Real.exp (a / 2))] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hI
  by_cases hz : I.toReal = 0
  · rw [hz, Real.log_zero]
    positivity
  · have hpos : 0 < I.toReal := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hz)
    have hl := Real.log_le_log hpos hi
    rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp] at hl
    linarith

end HeatKernel
