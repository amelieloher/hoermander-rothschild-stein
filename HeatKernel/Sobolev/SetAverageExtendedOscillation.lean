-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.SetAverageOscillation
import Mathlib.Tactic

/-! # Nonnegative integral form of set-average oscillation bounds -/

@[expose] public section
open Set MeasureTheory
open scoped ENNReal
namespace HeatKernel.Sobolev

/-- The normalized set-average oscillation bound in nonnegative integral form. -/
theorem ofReal_sq_sub_setAverage_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {U : Set α} (hU : MeasurableSet U) (hUpos : 0 < μ.real U)
    {f : α → ℝ} (hf : IntegrableOn f U μ)
    (hf₂ : IntegrableOn (fun x => f x ^ 2) U μ) (z c : ℝ) :
    ENNReal.ofReal ((z - (∫ x in U, f x ∂μ) / μ.real U) ^ 2) ≤
      2 * ENNReal.ofReal ((z - c) ^ 2) +
        2 * (μ U)⁻¹ * ∫⁻ x in U, ENNReal.ofReal ((f x - c) ^ 2) ∂μ := by
  have hfinite : μ U ≠ ⊤ := (ENNReal.toReal_pos_iff.mp hUpos).2.ne
  have hvar : IntegrableOn (fun x => (f x - c) ^ 2) U μ := by
    convert (hf₂.sub (hf.mul_const (2 * c))).add
      ((integrableOn_const hfinite : IntegrableOn (fun _ : α => (1 : ℝ)) U μ).mul_const (c ^ 2)) using 1
    funext x
    simp only [Pi.add_apply, Pi.sub_apply, one_mul]
    ring
  have hI := ofReal_integral_eq_lintegral_ofReal (f := fun x => (f x - c) ^ 2) hvar
    (Filter.Eventually.of_forall (fun x => sq_nonneg _))
  have hnum : ENNReal.ofReal (2 / μ.real U) = 2 * (μ U)⁻¹ := by
    change ENNReal.ofReal (2 / (μ U).toReal) = _
    rw [ENNReal.ofReal_div_of_pos (x := 2) (y := (μ U).toReal) (by exact hUpos), ENNReal.ofReal_ofNat, ENNReal.ofReal_toReal hfinite]
    rfl
  have H := ENNReal.ofReal_le_ofReal (sq_sub_setAverage_le hU hUpos hf hf₂ z c)
  rw [ENNReal.ofReal_add (mul_nonneg (by norm_num) (sq_nonneg _))
    (mul_nonneg (div_nonneg (by norm_num) hUpos.le) (integral_nonneg (fun _ => sq_nonneg _))),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ENNReal.ofReal_mul (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hUpos.le), hnum, hI] at H
  simpa only [ENNReal.ofReal_ofNat] using H

end HeatKernel.Sobolev
