-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.TailInterpolation
import Mathlib.Tactic

/-!
# Interpolation with an energy bound

A quadratic moment and a scale-compatible weak power bound give a strong
subcritical estimate linear in the energy. On a ball with its normalized
measure, this is the normalized Sobolev estimate.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace HeatKernel.Sobolev

/-- The homogeneity of interpolation turns a quadratic energy into a q-th moment. -/
theorem interpolation_product_eq_energy_power {S K C q p : ℝ}
    (hS : 0 ≤ S) (hK : 0 ≤ K) (hq : 2 < q) (hqp : q < p) :
    C * S ^ ((p - q) / (p - 2)) * (K * S ^ (p / 2)) ^ ((q - 2) / (p - 2)) =
      (C * K ^ ((q - 2) / (p - 2))) * S ^ (q / 2) := by
  have hp₂ : p - 2 ≠ 0 := by linarith
  have he : (p - q) / (p - 2) + p / 2 * ((q - 2) / (p - 2)) = q / 2 := by
    field_simp
    ring
  rw [Real.mul_rpow hK (Real.rpow_nonneg hS _), ← Real.rpow_mul hS]
  calc
    _ = (C * K ^ ((q - 2) / (p - 2))) *
        (S ^ ((p - q) / (p - 2)) * S ^ (p / 2 * ((q - 2) / (p - 2)))) := by ring
    _ = _ := by
      rw [← Real.rpow_add' hS (by rw [he]; linarith :
        (p - q) / (p - 2) + p / 2 * ((q - 2) / (p - 2)) ≠ 0), he]

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- A quadratic moment and a compatible weak higher-power estimate control the strong moment. -/
theorem lintegral_abs_rpow_le_energy_power {u : α → ℝ}
    (hu : MemLp u 2 μ) {S K q p : ℝ} (hS : 0 ≤ S) (hK : 0 ≤ K)
    (hq : 2 < q) (hqp : q < p) (hL₂ : (∫ x, u x ^ 2 ∂μ) ≤ S)
    (htail : ∀ s, 0 < s → μ {x | s < |u x|} ≤
      ENNReal.ofReal ((K * S ^ (p / 2)) * s ^ (-p))) :
    (∫⁻ x, ENNReal.ofReal (|u x| ^ q) ∂μ) ≤
      ENNReal.ofReal (((1 / (1 - 2 / q) + 1 / (p / q - 1)) *
        K ^ ((q - 2) / (p - 2))) * S ^ (q / 2)) := by
  have hq₀ : 0 < q := by linarith
  have hd₁ : 0 < 1 - 2 / q := sub_pos.mpr ((div_lt_one hq₀).mpr hq)
  have hd₂ : 0 < p / q - 1 := sub_pos.mpr ((one_lt_div hq₀).mpr hqp)
  have hC : 0 ≤ 1 / (1 - 2 / q) + 1 / (p / q - 1) := by positivity
  have hα : 0 ≤ (p - q) / (p - 2) := by
    exact div_nonneg (sub_nonneg.mpr hqp.le) (by linarith)
  have h := lintegral_abs_rpow_le_of_memLp_two hu hq hqp
    (mul_nonneg hK (Real.rpow_nonneg hS _)) htail
  apply h.trans
  rw [← interpolation_product_eq_energy_power hS hK hq hqp]
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (integral_nonneg (fun x => sq_nonneg _)) hL₂ hα) hC)
    (Real.rpow_nonneg (mul_nonneg hK (Real.rpow_nonneg hS _)) _)

/-- The squared strong norm is bounded linearly by the energy. -/
theorem eLpNorm_sq_le_energy_of_weak_tail {u : α → ℝ}
    (hu : MemLp u 2 μ) {S K q p : ℝ} (hS : 0 ≤ S) (hK : 0 ≤ K)
    (hq : 2 < q) (hqp : q < p) (hL₂ : (∫ x, u x ^ 2 ∂μ) ≤ S)
    (htail : ∀ s, 0 < s → μ {x | s < |u x|} ≤
      ENNReal.ofReal ((K * S ^ (p / 2)) * s ^ (-p))) :
    eLpNorm u (ENNReal.ofReal q) μ ^ 2 ≤
      ENNReal.ofReal (((1 / (1 - 2 / q) + 1 / (p / q - 1)) *
        K ^ ((q - 2) / (p - 2))) ^ (2 / q) * S) := by
  have hq₀ : 0 < q := by linarith
  have hd₁ : 0 < 1 - 2 / q := sub_pos.mpr ((div_lt_one hq₀).mpr hq)
  have hd₂ : 0 < p / q - 1 := sub_pos.mpr ((one_lt_div hq₀).mpr hqp)
  have hC : 0 ≤ (1 / (1 - 2 / q) + 1 / (p / q - 1)) *
      K ^ ((q - 2) / (p - 2)) := by positivity
  have h := ENNReal.rpow_le_rpow
    (lintegral_abs_rpow_le_energy_power hu hS hK hq hqp hL₂ htail)
    (div_nonneg (by norm_num) hq₀.le : 0 ≤ 2 / q)
  rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hC (Real.rpow_nonneg hS _))
    (div_nonneg (by norm_num) hq₀.le)] at h
  rw [Real.mul_rpow hC (Real.rpow_nonneg hS _), ← Real.rpow_mul hS,
    show q / 2 * (2 / q) = 1 by field_simp,
    Real.rpow_one] at h
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hq₀).ne'
    ENNReal.ofReal_ne_top hu.aestronglyMeasurable, ENNReal.toReal_ofReal hq₀.le]
  simp_rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hq₀.le]
  rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul, show 1 / q * 2 = 2 / q by ring]
  exact h

end HeatKernel.Sobolev
