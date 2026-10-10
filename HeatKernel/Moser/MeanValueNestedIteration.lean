-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueNormIteration
public import HeatKernel.Moser.MeanValueCutoffConstants
import Mathlib.Tactic

/-! # Mean-value iteration on nested integration domains -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Filter
open scoped ENNReal Topology
namespace HeatKernel

/-- Cutoff energy steps on varying outer measures bound the essential supremum on
any common inner measure. Both the measure inclusions and energy steps are explicit. -/
theorem eLpNormEssSup_le_of_nested_cutoff_iteration
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (μouter : ℕ → Measure α)
    {f : α → ℝ} {Y : ℕ → ℝ} {C B δ χ : ℝ}
    (hC : 1 ≤ C) (hB : 1 ≤ B) (hδ : 0 < δ) (hδone : δ ≤ 1) (hχ : 1 < χ)
    (hY : 0 ≤ Y 0) (hμ : ∀ j, μ ≤ μouter j)
    (hnorm : ∀ j, eLpNorm f (ENNReal.ofReal (2 * χ ^ j)) (μouter j) ≤
      ENNReal.ofReal (Y j))
    (hstep : ∀ j, Y (j + 1) ≤ (C * B ^ j / δ ^ 2) ^ (1 / (2 * χ ^ j)) * Y j) :
    eLpNormEssSup f μ ≤ ENNReal.ofReal
      (Real.exp (((Real.log C - 2 * Real.log δ) / 2) * (1 - χ⁻¹)⁻¹ +
        (Real.log B / 2) * (χ⁻¹ / (1 - χ⁻¹) ^ 2)) * Y 0) := by
  have hχpos : 0 < χ := zero_lt_one.trans hχ
  have hp : ∀ j : ℕ, 0 < 2 * χ ^ j := fun j => by positivity
  have hptop : Tendsto (fun j : ℕ => 2 * χ ^ j) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hχ).const_mul_atTop (by norm_num)
  apply eLpNormEssSup_le_of_unbounded_exponents μ hp hptop
  intro j
  calc
    _ ≤ eLpNorm f (ENNReal.ofReal (2 * χ ^ j)) (μouter j) :=
      eLpNorm_mono_measure f (hμ j)
    _ ≤ ENNReal.ofReal (Y j) := hnorm j
    _ ≤ _ := ENNReal.ofReal_le_ofReal
      (le_cutoff_iteration_constant_mul hC hB hδ hδone hχ hY hstep j)

/-- Finite integral norms themselves supply the outer norm sequence. -/
theorem eLpNormEssSup_le_of_finite_nested_cutoff_iteration
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (μouter : ℕ → Measure α)
    {f : α → ℝ} {C B δ χ : ℝ}
    (hC : 1 ≤ C) (hB : 1 ≤ B) (hδ : 0 < δ) (hδone : δ ≤ 1) (hχ : 1 < χ)
    (hμ : ∀ j, μ ≤ μouter j)
    (hfinite : ∀ j, eLpNorm f (ENNReal.ofReal (2 * χ ^ j)) (μouter j) < ⊤)
    (hstep : ∀ j,
      (eLpNorm f (ENNReal.ofReal (2 * χ ^ (j + 1))) (μouter (j + 1))).toReal ≤
        (C * B ^ j / δ ^ 2) ^ (1 / (2 * χ ^ j)) *
          (eLpNorm f (ENNReal.ofReal (2 * χ ^ j)) (μouter j)).toReal) :
    eLpNormEssSup f μ ≤ ENNReal.ofReal
      (Real.exp (((Real.log C - 2 * Real.log δ) / 2) * (1 - χ⁻¹)⁻¹ +
        (Real.log B / 2) * (χ⁻¹ / (1 - χ⁻¹) ^ 2)) *
        (eLpNorm f 2 (μouter 0)).toReal) := by
  have hnorm (j : ℕ) : eLpNorm f (ENNReal.ofReal (2 * χ ^ j)) (μouter j) ≤
      ENNReal.ofReal (eLpNorm f (ENNReal.ofReal (2 * χ ^ j)) (μouter j)).toReal := by
    rw [ENNReal.ofReal_toReal (hfinite j).ne]
  simpa only [pow_zero, mul_one, ENNReal.ofReal_ofNat] using
    eLpNormEssSup_le_of_nested_cutoff_iteration μ μouter hC hB hδ hδone hχ
      ENNReal.toReal_nonneg hμ hnorm hstep

end HeatKernel
