-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.TentLayers
import Mathlib.Tactic

/-! # Polynomial moments of the two tent layer weights -/

@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace HeatKernel.Sobolev

/-- The volume moment for the linear tent. -/
theorem integral_unit_pow (Q : ℕ) :
    (∫ s in Ioo (0 : ℝ) 1, s ^ Q) = 1 / ((Q : ℝ) + 1) := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    _root_.integral_pow]
  simp

/-- The volume moment for the squared tent. -/
theorem integral_unit_tent_mul_pow (Q : ℕ) :
    (∫ s in Ioo (0 : ℝ) 1, 2 * (1 - s) * s ^ Q) =
      2 / (((Q : ℝ) + 1) * ((Q : ℝ) + 2)) := by
  have he : (fun s : ℝ => 2 * (1 - s) * s ^ Q) =
      fun s => 2 * s ^ Q - 2 * s ^ (Q + 1) := by
    funext s
    rw [pow_succ]
    ring
  rw [he, integral_sub (f := fun s : ℝ => 2 * s ^ Q) (g := fun s : ℝ => 2 * s ^ (Q + 1))
    ((continuous_const.mul (continuous_id.pow Q)).integrableOn_Icc.mono_set Ioo_subset_Icc_self)
    ((continuous_const.mul (continuous_id.pow (Q + 1))).integrableOn_Icc.mono_set Ioo_subset_Icc_self),
    integral_const_mul, integral_const_mul, integral_unit_pow, integral_unit_pow]
  push_cast
  have h1 : (Q : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (Q : ℝ) + 2 ≠ 0 := by positivity
  field_simp
  ring

/-- The nonnegative integral volume moment for the linear tent. -/
theorem lintegral_unit_pow (Q : ℕ) :
    (∫⁻ s in Ioo (0 : ℝ) 1, ENNReal.ofReal (s ^ Q)) =
      ENNReal.ofReal (1 / ((Q : ℝ) + 1)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (f := fun s : ℝ => s ^ Q)
    ((continuous_id.pow Q).integrableOn_Icc.mono_set Ioo_subset_Icc_self)
    (ae_restrict_of_forall_mem measurableSet_Ioo (fun s hs => pow_nonneg hs.1.le Q)),
    integral_unit_pow]

/-- The nonnegative integral volume moment for the squared tent. -/
theorem lintegral_unit_tent_mul_pow (Q : ℕ) :
    (∫⁻ s in Ioo (0 : ℝ) 1, ENNReal.ofReal (2 * (1 - s) * s ^ Q)) =
      ENNReal.ofReal (2 / (((Q : ℝ) + 1) * ((Q : ℝ) + 2))) := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((by fun_prop : Continuous (fun s : ℝ => 2 * (1 - s) * s ^ Q)).integrableOn_Icc.mono_set
      Ioo_subset_Icc_self)
    (ae_restrict_of_forall_mem measurableSet_Ioo (fun s hs => by change 0 ≤ 2 * (1 - s) * s ^ Q; exact mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hs.2.le)) (pow_nonneg hs.1.le Q))),
    integral_unit_tent_mul_pow]

end HeatKernel.Sobolev
