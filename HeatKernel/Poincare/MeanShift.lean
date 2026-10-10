-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.MeanPowerIntegral
public import Mathlib.Analysis.MeanInequalitiesPow

/-! Quantitative replacement of an auxiliary constant by the integral mean. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace HeatKernel

/-- The convex power estimate for a sum of two nonnegative real numbers. -/
theorem add_rpow_le_two_rpow_mul_add {a b p : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hp : 1 ≤ p) :
    (a + b) ^ p ≤ (2 : ℝ) ^ (p - 1) * (a ^ p + b ^ p) := by
  exact_mod_cast NNReal.rpow_add_le_mul_rpow_add_rpow ⟨a, ha⟩ ⟨b, hb⟩ hp

/-- Replacing an arbitrary constant by the mean costs at most 2^p in the power integral.
The left integral need not be known finite beforehand. -/
theorem lintegral_abs_sub_average_rpow_le_const {E : Type*} [MeasurableSpace E]
    {μ : Measure E} [IsFiniteMeasure μ] [NeZero μ] {f : E → ℝ} {p : ℝ}
    (hp : 1 ≤ p) (hf : Integrable f μ) (c : ℝ)
    (hfp : Integrable (fun x => |f x - c| ^ p) μ) :
    (∫⁻ x, ENNReal.ofReal (|f x - ⨍ y, f y ∂μ| ^ p) ∂μ) ≤
      ENNReal.ofReal ((2 : ℝ) ^ p) * ∫⁻ x, ENNReal.ofReal (|f x - c| ^ p) ∂μ := by
  let m := ⨍ y, f y ∂μ
  let F := fun x => ENNReal.ofReal (|f x - c| ^ p)
  let C := ENNReal.ofReal (|c - m| ^ p)
  let k := ENNReal.ofReal ((2 : ℝ) ^ (p - 1))
  have hF : AEMeasurable F μ := hfp.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hcp : Integrable (fun x => |c - f x| ^ p) μ := by
    simpa only [abs_sub_comm c] using hfp
  have hC : C ≤ (μ univ)⁻¹ * ∫⁻ x, F x ∂μ :=
    by simpa only [C, m, F, abs_sub_comm c] using
      ofReal_abs_sub_average_rpow_le_pair_integral hp hf c hcp
  have hmass : C * μ univ ≤ ∫⁻ x, F x ∂μ := by
    have hh := mul_le_mul_left hC (μ univ)
    have he : ((μ univ)⁻¹ * (∫⁻ x, F x ∂μ)) * μ univ = ∫⁻ x, F x ∂μ := by
      rw [mul_right_comm, ENNReal.inv_mul_cancel
        (Measure.measure_univ_ne_zero.mpr (NeZero.ne μ)) (measure_ne_top μ univ), one_mul]
    rwa [he] at hh
  have hk2 : k * 2 = ENNReal.ofReal ((2 : ℝ) ^ p) := by
    change ENNReal.ofReal ((2 : ℝ) ^ (p - 1)) * 2 = _
    rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)]
    congr 1
    calc
      (2 : ℝ) ^ (p - 1) * 2 = (2 : ℝ) ^ (p - 1) * (2 : ℝ) ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      _ = (2 : ℝ) ^ p := by rw [← Real.rpow_add (by norm_num)]; congr 1; ring
  calc
    (∫⁻ x, ENNReal.ofReal (|f x - m| ^ p) ∂μ) ≤ ∫⁻ x, k * (F x + C) ∂μ := by
      apply lintegral_mono
      intro x
      have ht := Real.rpow_le_rpow (abs_nonneg (f x - m)) (abs_sub_le (f x) c m)
        (le_trans zero_le_one hp)
      have hh := ht.trans (add_rpow_le_two_rpow_mul_add (abs_nonneg _) (abs_nonneg _) hp)
      have hn : 0 ≤ |f x - c| ^ p := Real.rpow_nonneg (abs_nonneg _) _
      have hn' : 0 ≤ |c - m| ^ p := Real.rpow_nonneg (abs_nonneg _) _
      have hh' := ENNReal.ofReal_le_ofReal hh
      rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (p - 1)),
        ENNReal.ofReal_add hn hn'] at hh'
      exact hh'
    _ = k * ((∫⁻ x, F x ∂μ) + C * μ univ) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left' hF, lintegral_const]
    _ ≤ k * ((∫⁻ x, F x ∂μ) + ∫⁻ x, F x ∂μ) :=
      mul_le_mul_right (add_le_add_right hmass _) k
    _ = ENNReal.ofReal ((2 : ℝ) ^ p) * ∫⁻ x, F x ∂μ := by
      rw [← two_mul, ← mul_assoc, hk2]

end HeatKernel
