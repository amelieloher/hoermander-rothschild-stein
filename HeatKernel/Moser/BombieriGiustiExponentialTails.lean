-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.BombieriGiustiMeasureNormalization
import Mathlib.Tactic

/-! # Exponential tails from signed logarithmic tails

The same logarithmic shift gives the upper tail of a rescaled positive function
and the upper tail of its reciprocal. Positivity is needed only almost everywhere
on the reference set. Real measure bounds are normalized by its positive mass.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace HeatKernel

/-- Rescaling by the negative logarithmic shift converts an exponential upper
tail into the corresponding signed logarithmic upper tail. -/
theorem exponential_tail_iff_logarithmic_upper_tail {v c ℓ : ℝ} (hv : 0 < v) :
    ENNReal.ofReal (Real.exp ℓ) < ENNReal.ofReal (Real.exp (-c) * v) ↔
      c + ℓ < Real.log v := by
  rw [ENNReal.ofReal_lt_ofReal_iff (h := mul_pos (Real.exp_pos _) hv)]
  have heq : Real.exp (-c) * v = Real.exp (Real.log v - c) := by
    rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hv, mul_comm]
  rw [heq, Real.exp_lt_exp]
  constructor <;> intro h <;> linarith

/-- Rescaling the reciprocal by the positive logarithmic shift converts its
exponential upper tail into the logarithmic lower tail of the function. -/
theorem reciprocal_exponential_tail_iff_logarithmic_lower_tail
    {v c ℓ : ℝ} (hv : 0 < v) :
    ENNReal.ofReal (Real.exp ℓ) < ENNReal.ofReal (Real.exp c / v) ↔
      Real.log v < c - ℓ := by
  rw [ENNReal.ofReal_lt_ofReal_iff (h := div_pos (Real.exp_pos _) hv)]
  have heq : Real.exp c / v = Real.exp (c - Real.log v) := by
    rw [Real.exp_sub, Real.exp_log hv]
  rw [heq, Real.exp_lt_exp]
  constructor <;> intro h <;> linarith

/-- A relative logarithmic upper-tail estimate supplies the exponential-tail
hypothesis for the rescaled positive function. -/
theorem measure_exponential_tail_le_of_logarithmic_upper_tail
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {V : Set α}
    {v : α → ℝ} {c A : ℝ}
    (hv : ∀ᵐ y ∂μ, y ∈ V → 0 < v y)
    (htail : ∀ ℓ : ℝ, 0 < ℓ →
      μ (V ∩ {y | c + ℓ < Real.log (v y)}) ≤ ENNReal.ofReal (A / ℓ) * μ V) :
    ∀ ℓ : ℝ, 0 < ℓ →
      μ (V ∩ {y | ENNReal.ofReal (Real.exp ℓ) <
        ENNReal.ofReal (Real.exp (-c) * v y)}) ≤ ENNReal.ofReal (A / ℓ) * μ V := by
  intro ℓ hℓ
  apply le_trans (measure_mono_ae ?_) (htail ℓ hℓ)
  filter_upwards [hv] with y hy hmem
  exact ⟨hmem.1, (exponential_tail_iff_logarithmic_upper_tail (hy hmem.1)).mp hmem.2⟩

/-- A relative logarithmic lower-tail estimate supplies the exponential-tail
hypothesis for the rescaled reciprocal, using the same shift. -/
theorem measure_reciprocal_exponential_tail_le_of_logarithmic_lower_tail
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {V : Set α}
    {v : α → ℝ} {c A : ℝ}
    (hv : ∀ᵐ y ∂μ, y ∈ V → 0 < v y)
    (htail : ∀ ℓ : ℝ, 0 < ℓ →
      μ (V ∩ {y | Real.log (v y) < c - ℓ}) ≤ ENNReal.ofReal (A / ℓ) * μ V) :
    ∀ ℓ : ℝ, 0 < ℓ →
      μ (V ∩ {y | ENNReal.ofReal (Real.exp ℓ) <
        ENNReal.ofReal (Real.exp c / v y)}) ≤ ENNReal.ofReal (A / ℓ) * μ V := by
  intro ℓ hℓ
  apply le_trans (measure_mono_ae ?_) (htail ℓ hℓ)
  filter_upwards [hv] with y hy hmem
  exact ⟨hmem.1, (reciprocal_exponential_tail_iff_logarithmic_lower_tail
    (hy hmem.1)).mp hmem.2⟩

end HeatKernel
