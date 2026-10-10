-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.BombieriGiustiExponentialTails
import Mathlib.Tactic

/-! # Finite moments of positively perturbed reciprocals -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace HeatKernel

/-- A positive perturbation of a nonnegative function has a bounded reciprocal.
Every nonnegative power of its rescaled reciprocal therefore has a finite moment
on a finite-measure set. No regularity of the original function is needed. -/
theorem lintegral_rescaled_reciprocal_rpow_ne_top_of_nonneg
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {V : Set α}
    {u : α → ℝ} {c ε p : ℝ} (hfinite : μ V ≠ ⊤)
    (hnonneg : ∀ᵐ y ∂μ.restrict V, 0 ≤ u y) (hε : 0 < ε) (hp : 0 ≤ p) :
    (∫⁻ y in V, ENNReal.ofReal (Real.exp c / (u y + ε)) ^ p ∂μ) ≠ ⊤ := by
  have hbound : ∀ᵐ y ∂μ.restrict V,
      ENNReal.ofReal (Real.exp c / (u y + ε)) ^ p ≤
        ENNReal.ofReal (Real.exp c / ε) ^ p := by
    filter_upwards [hnonneg] with y hy
    apply ENNReal.rpow_le_rpow _ hp
    exact ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_left (Real.exp_pos c).le hε (by linarith))
  have hmoment :
      (∫⁻ y in V, ENNReal.ofReal (Real.exp c / (u y + ε)) ^ p ∂μ) ≤
        ENNReal.ofReal (Real.exp c / ε) ^ p * μ V := by
    calc
      _ ≤ ∫⁻ _y in V, ENNReal.ofReal (Real.exp c / ε) ^ p ∂μ :=
        lintegral_mono_ae hbound
      _ = _ := by rw [lintegral_const, Measure.restrict_apply_univ]
  exact ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hp ENNReal.ofReal_ne_top) hfinite)
    hmoment

end HeatKernel
