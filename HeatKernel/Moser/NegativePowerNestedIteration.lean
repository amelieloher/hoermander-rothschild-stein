-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueNormIteration
public import HeatKernel.Moser.NegativePowerIterationCosts

/-! Essential reciprocal bounds from nested negative-power norm iteration. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace HeatKernel

/-- A cutoff factor at an arbitrary positive initial exponent has a geometric
logarithmic cost; its constants do not depend on that exponent. -/
theorem negative_power_cutoff_factor_eq_exp {C B δ χ p : ℝ}
    (hC : 0 < C) (hB : 0 < B) (hδ : 0 < δ) (hχ : 0 < χ) (j : ℕ) :
    (C * B ^ j / δ ^ 2) ^ (1 / (p * χ ^ j)) =
      Real.exp (((Real.log C - 2 * Real.log δ) + Real.log B * j) * (χ⁻¹) ^ j / p) := by
  rw [Real.rpow_def_of_pos (by positivity),
    Real.log_div (by positivity) (by positivity),
    Real.log_mul hC.ne' (pow_ne_zero _ hB.ne'), Real.log_pow, Real.log_pow]
  congr 1
  rw [inv_pow]
  field_simp
  ring

/-- Nested negative-power steps at every growing exponent control the essential
supremum on a common inner measure. Measure inclusions and norm steps are explicit. -/
theorem eLpNormEssSup_le_of_negative_power_nested_iteration
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (μouter : ℕ → Measure α)
    {f : α → ℝ} {Y : ℕ → ℝ} {χ A B p : ℝ}
    (hχ : 1 < χ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hp : 0 < p) (hY : 0 ≤ Y 0)
    (hμ : ∀ j, μ ≤ μouter j)
    (hnorm : ∀ j, eLpNorm f (ENNReal.ofReal (p * χ ^ j)) (μouter j) ≤ ENNReal.ofReal (Y j))
    (hstep : ∀ j, Y (j + 1) ≤ Real.exp ((A + B * j) * (χ⁻¹) ^ j / p) * Y j) :
    eLpNormEssSup f μ ≤ ENNReal.ofReal
      (Real.exp ((A / (1 - χ⁻¹) + B * χ⁻¹ / (1 - χ⁻¹) ^ 2) / p) * Y 0) := by
  have hχpos : 0 < χ := zero_lt_one.trans hχ
  have ht : Tendsto (fun j : ℕ => p * χ ^ j) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hχ).const_mul_atTop hp
  have h := eLpNormEssSup_le_of_geometric_norm_iteration μ (fun j => by positivity) ht
    (inv_nonneg.mpr hχpos.le) ((inv_lt_one₀ hχpos).mpr hχ)
    (div_nonneg hA hp.le) (div_nonneg hB hp.le) hY
    (fun j => (eLpNorm_mono_measure f (hμ j)).trans (hnorm j)) (by
      intro j
      convert hstep j using 1
      congr 2
      ring)
  have hcost : (A / p) * (1 - χ⁻¹)⁻¹ + (B / p) * (χ⁻¹ / (1 - χ⁻¹) ^ 2) =
      (A / (1 - χ⁻¹) + B * χ⁻¹ / (1 - χ⁻¹) ^ 2) / p := by ring
  simpa only [hcost] using h

/-- Cutoff-energy norm steps yield an essential bound for every positive initial
exponent, with one explicit accumulated constant independent of the exponent. -/
theorem eLpNormEssSup_le_of_negative_power_cutoff_iteration
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (μouter : ℕ → Measure α)
    {f : α → ℝ} {Y : ℕ → ℝ} {C B δ χ p : ℝ}
    (hC : 1 ≤ C) (hB : 1 ≤ B) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hχ : 1 < χ) (hp : 0 < p) (hY : 0 ≤ Y 0) (hμ : ∀ j, μ ≤ μouter j)
    (hnorm : ∀ j, eLpNorm f (ENNReal.ofReal (p * χ ^ j)) (μouter j) ≤ ENNReal.ofReal (Y j))
    (hstep : ∀ j, Y (j + 1) ≤ (C * B ^ j / δ ^ 2) ^ (1 / (p * χ ^ j)) * Y j) :
    eLpNormEssSup f μ ≤ ENNReal.ofReal
      (Real.exp (((Real.log C - 2 * Real.log δ) / (1 - χ⁻¹) +
        Real.log B * χ⁻¹ / (1 - χ⁻¹) ^ 2) / p) * Y 0) := by
  have hA : 0 ≤ Real.log C - 2 * Real.log δ := by
    have := Real.log_nonneg hC
    have := Real.log_nonpos hδ.le hδ1
    linarith
  apply eLpNormEssSup_le_of_negative_power_nested_iteration μ μouter hχ hA
    (Real.log_nonneg hB) hp hY hμ hnorm
  intro j
  simpa only [negative_power_cutoff_factor_eq_exp (zero_lt_one.trans_le hC)
    (zero_lt_one.trans_le hB) hδ (zero_lt_one.trans hχ)] using hstep j

end HeatKernel
