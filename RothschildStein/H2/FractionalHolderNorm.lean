-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.FractionalHolder
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal NNReal

namespace RothschildStein.H2

/-- Nonnegativity of the explicit fractional seminorm constant. -/
theorem fractionalSemiConstant_nonneg {C κ R α ν : ℝ} (hC : 0 < C)
    (hκ : 0 < κ) (hR : 0 < R) (hν : 0 < ν) (hαν : α < ν) :
    0 ≤ fractionalSemiConstant C κ R α ν := by
  have hcν := (volumeIntegralConstant_pos hC hν).le
  have hcα := (volumeIntegralConstant_pos hC (sub_pos.mpr hαν)).le
  unfold fractionalSemiConstant
  positivity

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Full fractional-integral Hölder bound with explicit constant, linear in A+S (BB Theorem 7.14, p. 305). -/
theorem SupportedKernel.fractional_holder_norm_le {D : LocDoubling X} {E G : Set X}
    {β ν A S R : ℝ} {K : X → X → ℝ} (hK : SupportedKernel D E G β ν A S R K)
    {α : ℝ≥0} (hα : 0 < α) (hαβ : (α : ℝ) ≤ β) (hαν : (α : ℝ) < ν)
    {f : X → ℝ} (hf : AEStronglyMeasurable f (D.μ.restrict G))
    {M : ℝ} (hM : 0 ≤ M) (hfb : ∀ᵐ y ∂D.μ.restrict G, |f y| ≤ M) :
    boundedHolderNorm α E (fractionalIntegral D.μ G K f) ≤
      ENNReal.ofReal (fractionalHolderConstant D.C_D D.κ R α ν * (A + S) * M) := by
  have hαr : 0 < (α : ℝ) := hα
  have hν : 0 < ν := hαr.trans hαν
  have hC := fractionalSemiConstant_nonneg (C := D.C_D) (by linarith [D.one_lt_C_D]) D.κ_pos hK.radius_pos hν hαν
  have hAM : 0 ≤ (A + S) * M := mul_nonneg (add_nonneg hK.kernel.A_nonneg hK.kernel.S_nonneg) hM
  have hsemi := holderSemi_le_of_bound (δ := α) (mul_nonneg (mul_nonneg hC (add_nonneg hK.kernel.A_nonneg hK.kernel.S_nonneg)) hM)
    (fun x hx y hy => hK.fractional_difference_le hαr hαβ hαν hf hM hfb hx hy)
  have hsup := holderSup_le_of_bound (fun x hx => hK.fractional_abs_le hν hf hM hfb hx)
  have hcν := (volumeIntegralConstant_pos (C := D.C_D) (by linarith [D.one_lt_C_D]) hν).le
  have hRν := Real.rpow_nonneg hK.radius_pos.le ν
  have hc : 0 ≤ A * M * volumeIntegralConstant D.C_D ν * R ^ ν :=
    mul_nonneg (mul_nonneg (mul_nonneg hK.kernel.A_nonneg hM) hcν) hRν
  unfold boundedHolderNorm
  calc
    _ ≤ ENNReal.ofReal (A * M * volumeIntegralConstant D.C_D ν * R ^ ν) +
        ENNReal.ofReal (fractionalSemiConstant D.C_D D.κ R α ν * (A + S) * M) := add_le_add hsup hsemi
    _ = ENNReal.ofReal (A * M * volumeIntegralConstant D.C_D ν * R ^ ν +
        fractionalSemiConstant D.C_D D.κ R α ν * (A + S) * M) := (ENNReal.ofReal_add hc (by nlinarith [mul_nonneg hC hAM])).symm
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      unfold fractionalHolderConstant
      have he := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hK.kernel.S_nonneg : A ≤ A + S)
        (mul_nonneg hM (mul_nonneg hcν hRν))
      nlinarith

end RothschildStein.H2
