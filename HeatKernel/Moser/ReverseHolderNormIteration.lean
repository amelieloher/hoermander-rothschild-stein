-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.NegativePowerIterationCosts
public import HeatKernel.Moser.ReverseHolderCoefficients
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-! Finite reverse-Hölder iteration for norms, including vanishing initial norms. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
open MeasureTheory Finset
open scoped BigOperators
namespace HeatKernel

/-- A finite multiplicative recurrence has a uniform endpoint cost without
taking logarithms of the iterated quantities. -/
theorem reverse_holder_norm_bound_of_finite_steps
    {Y : ℕ → ℝ} {q A B p p₀ : ℝ}
    (hq : 0 ≤ q) (hq1 : q < 1) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hp : 0 < p) (hp₀ : 0 < p₀) (hhalf : p ≤ p₀ / 2)
    (hY : 0 ≤ Y 0) (n : ℕ)
    (hstep : ∀ j < n, Y (j + 1) ≤
      Real.exp ((A + B * j) * q ^ j / p) * Y j) :
    Y n ≤ Real.exp (2 * (1 / p - 1 / p₀) *
      (A / (1 - q) + B * q / (1 - q) ^ 2)) * Y 0 := by
  have hfinite : ∀ m ≤ n, Y m ≤
      Real.exp (∑ j ∈ range m, (A + B * j) * q ^ j / p) * Y 0 := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      calc
        Y (m + 1) ≤ Real.exp ((A + B * m) * q ^ m / p) * Y m :=
          hstep m (Nat.lt_of_succ_le hm)
        _ ≤ Real.exp ((A + B * m) * q ^ m / p) *
            (Real.exp (∑ j ∈ range m, (A + B * j) * q ^ j / p) * Y 0) :=
          mul_le_mul_of_nonneg_left (ih (Nat.le_of_succ_le hm)) (Real.exp_pos _).le
        _ = _ := by rw [sum_range_succ, Real.exp_add]; ring
  have hcost := sum_negative_power_iteration_cost_le hq hq1 hA hB hp n
  have hK : 0 ≤ A / (1 - q) + B * q / (1 - q) ^ 2 := by positivity
  exact (hfinite n le_rfl).trans (mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (hcost.trans
      (reverse_holder_cost_le_exponent_difference hp hp₀ hhalf hK))) hY)

/-- Normalization by the larger cylinder leaves inner mass at most one.
Endpoint Hölder comparison therefore completes the finite iteration with no
additional volume factor. -/
theorem eLpNorm_le_of_reverse_holder_finite_iteration_of_mass_le_one
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (hμ : μ Set.univ ≤ 1)
    {f : α → ℝ} {Y : ℕ → ℝ} {q A B p p₀ χ : ℝ}
    (hq : 0 ≤ q) (hq1 : q < 1) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hp : 0 < p) (hp₀ : 0 < p₀) (hhalf : p ≤ p₀ / 2)
    (hY : 0 ≤ Y 0) (n : ℕ) (hend : p₀ ≤ p * χ ^ n)
    (hnorm : eLpNorm f (ENNReal.ofReal (p * χ ^ n)) μ ≤ ENNReal.ofReal (Y n))
    (hstep : ∀ j < n, Y (j + 1) ≤
      Real.exp ((A + B * j) * q ^ j / p) * Y j) :
    eLpNorm f (ENNReal.ofReal p₀) μ ≤ ENNReal.ofReal
      (Real.exp (2 * (1 / p - 1 / p₀) *
        (A / (1 - q) + B * q / (1 - q) ^ 2)) * Y 0) := by
  have hcompare := eLpNorm_le_eLpNorm_mul_rpow_measure_univ_of_pos
    (f := f) (μ := μ) (ENNReal.ofReal_le_ofReal hend) (ENNReal.ofReal_pos.mpr hp₀)
  simp only [ENNReal.toReal_ofReal hp₀.le,
    ENNReal.toReal_ofReal (hp₀.le.trans hend)] at hcompare
  have hmass : μ Set.univ ^ (1 / p₀ - 1 / (p * χ ^ n)) ≤ 1 := by
    simpa only [ENNReal.one_rpow] using ENNReal.rpow_le_rpow hμ
      (sub_nonneg.mpr (one_div_le_one_div_of_le hp₀ hend))
  have hnorm' : eLpNorm f (ENNReal.ofReal p₀) μ ≤
      eLpNorm f (ENNReal.ofReal (p * χ ^ n)) μ :=
    hcompare.trans ((mul_le_mul' le_rfl hmass).trans_eq (mul_one _))
  exact hnorm'.trans (hnorm.trans (ENNReal.ofReal_le_ofReal
    (reverse_holder_norm_bound_of_finite_steps hq hq1 hA hB hp hp₀ hhalf hY n hstep)))

end HeatKernel
