-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.RegularizedHolder

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal NNReal

namespace RothschildStein.H2

/-- Positivity bookkeeping for the explicit Hölder constant. -/
theorem regularizedHolderConstant_nonneg {β δ C θ₁ θ₂ : ℝ} (hC : 0 < C)
    (hδ : 0 < δ) (hδβ : δ < β) (hθ₁ : 0 ≤ θ₁) (hθ₂ : 0 ≤ θ₂) : 0 ≤ regularizedHolderConstant β δ C θ₁ θ₂ := by
  have h₁ := (volumeIntegralConstant_pos hC (sub_pos.mpr hδβ)).le
  have h₂ := (volumeIntegralConstant_pos hC hδ).le
  unfold regularizedHolderConstant cancellationBoundaryConstant
  positivity

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The exact seminorm estimate, BB pp. 302–304. -/
theorem SupportedKernel.regularized_seminorm_le {D : LocDoubling X} {E G : Set X}
    {β A S R C_K : ℝ} {K : X → X → ℝ} (hK : SupportedKernel D E G β 0 A S R K)
    (d : TruncDist D) (hCan : ShellCancellation D.μ E G d.d' K C_K)
    {δ : ℝ≥0} (hδ : 0 < δ) (hδβ : (δ : ℝ) < β) {f : X → ℝ} (hf : BoundedHolder δ G f) :
    holderSemi δ E (regularizedIntegral D.μ G K f) ≤
      ENNReal.ofReal (regularizedHolderConstant β δ D.C_D d.θ₁ d.θ₂ * (A + S + C_K)) * holderSemi δ G f := by
  have hC := regularizedHolderConstant_nonneg (C := D.C_D) (by linarith [D.one_lt_C_D])
    (show 0 < (δ : ℝ) from hδ) hδβ d.θ₁_pos.le (d.θ₁_pos.trans_le d.θ₁_le).le
  have hsum := add_nonneg (add_nonneg hK.kernel.A_nonneg hK.kernel.S_nonneg) hCan.1
  have he := holderSemi_le_of_bound (δ := δ)
    (mul_nonneg (mul_nonneg hC hsum) (show 0 ≤ (holderSemi δ G f).toReal from ENNReal.toReal_nonneg)) (by
      intro x hx y hy
      have hb := hK.regularized_difference_le d hCan hδ hδβ hf hy hx
      simpa only [dist_comm y x] using hb)
  simpa only [ENNReal.ofReal_mul (mul_nonneg hC hsum), ENNReal.ofReal_toReal hf.parts.2.ne] using he

/-- The full regularized norm is controlled by the input
seminorm, with the explicit constants for this estimate. -/
theorem SupportedKernel.regularized_holder_norm_le {D : LocDoubling X} {E G : Set X}
    {β A S R C_K : ℝ} {K : X → X → ℝ} (hK : SupportedKernel D E G β 0 A S R K)
    (d : TruncDist D) (hCan : ShellCancellation D.μ E G d.d' K C_K)
    {δ : ℝ≥0} (hδ : 0 < δ) (hδβ : (δ : ℝ) < β) {f : X → ℝ} (hf : BoundedHolder δ G f) :
    boundedHolderNorm δ E (regularizedIntegral D.μ G K f) ≤
      ENNReal.ofReal (regularizedHolderConstant β δ D.C_D d.θ₁ d.θ₂ * (A + S + C_K) +
        volumeIntegralConstant D.C_D δ * A * R ^ (δ : ℝ)) * holderSemi δ G f := by
  have hC := regularizedHolderConstant_nonneg (C := D.C_D) (by linarith [D.one_lt_C_D])
    (show 0 < (δ : ℝ) from hδ) hδβ d.θ₁_pos.le (d.θ₁_pos.trans_le d.θ₁_le).le
  have hsum := add_nonneg (add_nonneg hK.kernel.A_nonneg hK.kernel.S_nonneg) hCan.1
  have hsupC : 0 ≤ volumeIntegralConstant D.C_D δ * A * R ^ (δ : ℝ) :=
    mul_nonneg (mul_nonneg (volumeIntegralConstant_pos (C := D.C_D) (by linarith [D.one_lt_C_D])
      (show 0 < (δ : ℝ) from hδ)).le hK.kernel.A_nonneg) (Real.rpow_nonneg hK.radius_pos.le _)
  have hs := holderSup_le_of_bound (A := E) (f := regularizedIntegral D.μ G K f)
    (M := volumeIntegralConstant D.C_D δ * A * R ^ (δ : ℝ) * (holderSemi δ G f).toReal) (by
      intro x hx
      have he := hK.regularized_abs_le hδ hf hx
      simp only [zero_add] at he
      convert he using 1; ring)
  have hs' : holderSup E (regularizedIntegral D.μ G K f) ≤
      ENNReal.ofReal (volumeIntegralConstant D.C_D δ * A * R ^ (δ : ℝ)) * holderSemi δ G f := by
    simpa only [ENNReal.ofReal_mul hsupC, ENNReal.ofReal_toReal hf.parts.2.ne] using hs
  have hh := hK.regularized_seminorm_le d hCan hδ hδβ hf
  unfold boundedHolderNorm
  calc
    _ ≤ _ := add_le_add hs' hh
    _ = _ := by rw [← add_mul, ← ENNReal.ofReal_add hsupC (mul_nonneg hC hsum), add_comm]

/-- The regularized singular operator preserves bounded Hölder input. -/
theorem SupportedKernel.regularized_boundedHolder {D : LocDoubling X} {E G : Set X}
    {β A S R C_K : ℝ} {K : X → X → ℝ} (hK : SupportedKernel D E G β 0 A S R K)
    (d : TruncDist D) (hCan : ShellCancellation D.μ E G d.d' K C_K)
    {δ : ℝ≥0} (hδ : 0 < δ) (hδβ : (δ : ℝ) < β) {f : X → ℝ} (hf : BoundedHolder δ G f) :
    BoundedHolder δ E (regularizedIntegral D.μ G K f) :=
  (hK.regularized_holder_norm_le d hCan hδ hδβ hf).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf.parts.2)

end RothschildStein.H2
