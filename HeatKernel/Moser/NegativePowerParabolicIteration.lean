-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.NegativePowerNestedIteration
public import HeatKernel.Moser.NegativePowerCoefficients

/-! Uniform parabolic constants for reciprocal norm iteration. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace HeatKernel

/-- Parabolic reciprocal iteration has one constant independent of the initial
positive exponent, with the exact gap power `ν + 2`. The energy recurrence is explicit. -/
theorem exists_uniform_negative_power_iteration_constant {C B ν : ℝ}
    (hC : 1 ≤ C) (hB : 1 ≤ B) (hν : 0 < ν) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ {α : Type*} [MeasurableSpace α]
      (μ : Measure α) (μouter : ℕ → Measure α) (f : α → ℝ) (Y : ℕ → ℝ)
      (δ p : ℝ), 0 < δ → δ ≤ 1 → 0 < p → 0 ≤ Y 0 →
      (∀ j, μ ≤ μouter j) →
      (∀ j, eLpNorm f (ENNReal.ofReal (p * (1 + 2 / ν) ^ j)) (μouter j) ≤
        ENNReal.ofReal (Y j)) →
      (∀ j, Y (j + 1) ≤ (C * B ^ j / δ ^ 2) ^ (1 / (p * (1 + 2 / ν) ^ j)) * Y j) →
      eLpNormEssSup f μ ≤ ENNReal.ofReal ((K / δ ^ (ν + 2)) ^ (1 / p) * Y 0) := by
  let K := Real.exp (Real.log C * (ν + 2) / 2 + Real.log B * ν * (ν + 2) / 4)
  have hK : 1 ≤ K := Real.one_le_exp_iff.mpr (by
    have := Real.log_nonneg hC
    have := Real.log_nonneg hB
    positivity)
  refine ⟨K, hK, ?_⟩
  intro α _ μ μouter f Y δ p hδ hδ1 hp hY hμ hnorm hstep
  have hχ : 1 < 1 + 2 / ν := by
    have : 0 < 2 / ν := by positivity
    linarith
  have h := eLpNormEssSup_le_of_negative_power_cutoff_iteration μ μouter
    hC hB hδ hδ1 hχ hp hY hμ hnorm hstep
  have hn : ν + 2 ≠ 0 := by positivity
  have hq : (1 + 2 / ν)⁻¹ = ν / (ν + 2) := by field_simp [ne_of_gt hν, hn]
  obtain ⟨hg, hgj⟩ := negative_power_parabolic_geometric_coefficients hν
  have hcost :
      (Real.log C - 2 * Real.log δ) / (1 - (1 + 2 / ν)⁻¹) +
        Real.log B * (1 + 2 / ν)⁻¹ / (1 - (1 + 2 / ν)⁻¹) ^ 2 =
      (Real.log C - 2 * Real.log δ) * (ν + 2) / 2 + Real.log B * ν * (ν + 2) / 4 := by
    rw [hq]
    calc
      _ = (Real.log C - 2 * Real.log δ) * (1 - ν / (ν + 2))⁻¹ +
          Real.log B * ((ν / (ν + 2)) / (1 - ν / (ν + 2)) ^ 2) := by ring
      _ = _ := by rw [hg, hgj]; ring
  have heq : Real.exp (((Real.log C - 2 * Real.log δ) * (ν + 2) / 2 +
      Real.log B * ν * (ν + 2) / 4) / p) = (K / δ ^ (ν + 2)) ^ (1 / p) := by
    rw [Real.rpow_def_of_pos (by positivity), Real.log_div (Real.exp_ne_zero _) (by positivity),
      Real.log_rpow hδ]
    rw [Real.log_exp]
    congr 1
    ring
  simpa only [hcost, heq] using h

end HeatKernel
