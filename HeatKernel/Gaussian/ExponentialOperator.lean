-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Gaussian.MultiplicationOperator
public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-! # Exponential multiplication operators

Bounded measurable real weights define exponential multiplication on L².
Changing the sign of the parameter gives an inverse operator.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory
namespace HeatKernel.Gaussian

/-- A bounded logarithmic weight gives a uniform exponential multiplier bound. -/
theorem norm_exp_mul_le_of_abs_le {a B u : ℝ} (hu : |u| ≤ B) :
    ‖Real.exp (a * u)‖ ≤ Real.exp (|a| * B) := by
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc
    a * u ≤ |a * u| := le_abs_self _
    _ = |a| * |u| := abs_mul _ _
    _ ≤ |a| * B := mul_le_mul_of_nonneg_left hu (abs_nonneg _)

/-- The exponential of a bounded measurable real weight as an L∞ function. -/
def exponentialLp {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (ψ : α → ℝ) (hψ : AEStronglyMeasurable ψ μ) (B : ℝ)
    (hB : ∀ x, |ψ x| ≤ B) (a : ℝ) : Lp ℝ ⊤ μ :=
  (memLp_top_of_bound
    (Real.continuous_exp.comp_aestronglyMeasurable (aestronglyMeasurable_const.mul hψ))
    (Real.exp (|a| * B)) (Filter.Eventually.of_forall (fun x ↦ norm_exp_mul_le_of_abs_le (hB x)))).toLp _

/-- The exponential multiplier represents the pointwise exponential almost everywhere. -/
theorem coeFn_exponentialLp {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (ψ : α → ℝ) (hψ : AEStronglyMeasurable ψ μ) (B : ℝ)
    (hB : ∀ x, |ψ x| ≤ B) (a : ℝ) :
    exponentialLp μ ψ hψ B hB a =ᵐ[μ] fun x ↦ Real.exp (a * ψ x) :=
  MemLp.coeFn_toLp _

/-- Exponential multiplication on the real square-integrable space. -/
def exponentialMultiplication {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (ψ : α → ℝ) (hψ : AEStronglyMeasurable ψ μ) (B : ℝ)
    (hB : ∀ x, |ψ x| ≤ B) (a : ℝ) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  l2Multiplication (exponentialLp μ ψ hψ B hB a)

/-- Exponential multiplication has the expected almost everywhere action. -/
theorem coeFn_exponentialMultiplication {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (ψ : α → ℝ) (hψ : AEStronglyMeasurable ψ μ) (B : ℝ)
    (hB : ∀ x, |ψ x| ≤ B) (a : ℝ) (f : Lp ℝ 2 μ) :
    exponentialMultiplication μ ψ hψ B hB a f =ᵐ[μ] fun x ↦ Real.exp (a * ψ x) * f x := by
  filter_upwards [coeFn_l2Multiplication (exponentialLp μ ψ hψ B hB a) f,
    coeFn_exponentialLp μ ψ hψ B hB a] with x hx hy
  exact hx.trans (by rw [hy])

/-- Opposite exponential parameters give inverse multiplication operators. -/
theorem exponentialMultiplication_comp_neg_eq_id {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (ψ : α → ℝ) (hψ : AEStronglyMeasurable ψ μ) (B : ℝ)
    (hB : ∀ x, |ψ x| ≤ B) (a : ℝ) :
    (exponentialMultiplication μ ψ hψ B hB a).comp
      (exponentialMultiplication μ ψ hψ B hB (-a)) = ContinuousLinearMap.id ℝ (Lp ℝ 2 μ) := by
  apply l2Multiplication_comp_eq_id
  filter_upwards [coeFn_exponentialLp μ ψ hψ B hB a,
    coeFn_exponentialLp μ ψ hψ B hB (-a)] with x hx hy
  rw [hx, hy, ← Real.exp_add]
  simp

end HeatKernel.Gaussian
