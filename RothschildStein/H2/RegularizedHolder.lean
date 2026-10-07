-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.RegularizedSplit

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal NNReal

namespace RothschildStein.H2

/-- The exact explicit singular Hölder constant for this estimate. -/
def regularizedHolderConstant (β δ C θ₁ θ₂ : ℝ) : ℝ :=
  volumeIntegralConstant C (β - δ) + cancellationBoundaryConstant C θ₁ θ₂ +
    18 * volumeIntegralConstant C δ

/-- Each positive-exponent volume constant is at least one. -/
theorem volumeIntegralConstant_one_le {C α : ℝ} (hC : 1 < C) (hα : 0 < α) :
    1 ≤ volumeIntegralConstant C α := by
  have hd : 0 < 1 - (2 : ℝ) ^ (-α) :=
    sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hα))
  unfold volumeIntegralConstant
  apply (le_div_iff₀ hd).mpr
  have hp := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (-α)
  linarith

/-- Scaling a distance by c≥1 costs at most c for exponents ≤1. -/
theorem rpow_scaled_le {c t δ : ℝ} (hc : 1 ≤ c) (ht : 0 ≤ t) (hδ : δ ≤ 1) :
    (c * t) ^ δ ≤ c * t ^ δ := by
  rw [Real.mul_rpow (zero_le_one.trans hc) ht]
  have he := Real.rpow_le_rpow_of_exponent_le hc hδ
  rw [Real.rpow_one] at he
  exact mul_le_mul_of_nonneg_right he (Real.rpow_nonneg ht δ)

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Pointwise Hölder bound for the regularized singular integral,
BB Theorem 7.12, pp. 302–304, with open-shell truncations. -/
theorem SupportedKernel.regularized_difference_le {D : LocDoubling X} {E G : Set X}
    {β A S R C_K : ℝ} {K : X → X → ℝ} (hK : SupportedKernel D E G β 0 A S R K)
    (d : TruncDist D) (hCan : ShellCancellation D.μ E G d.d' K C_K)
    {δ : ℝ≥0} (hδ : 0 < δ) (hδβ : (δ : ℝ) < β) {f : X → ℝ} (hf : BoundedHolder δ G f)
    {x₀ x : X} (hx₀ : x₀ ∈ E) (hx : x ∈ E) :
    |regularizedIntegral D.μ G K f x - regularizedIntegral D.μ G K f x₀| ≤
      regularizedHolderConstant β δ D.C_D d.θ₁ d.θ₂ * (A + S + C_K) *
        (holderSemi δ G f).toReal * dist x₀ x ^ (δ : ℝ) := by
  have hδr : 0 < (δ : ℝ) := hδ
  have hδ₁ : (δ : ℝ) ≤ 1 := hδβ.le.trans hK.kernel.β_le_one
  have hcδ := (volumeIntegralConstant_pos (C := D.C_D) (by linarith [D.one_lt_C_D]) hδr).le
  have hcd := (volumeIntegralConstant_pos (C := D.C_D) (by linarith [D.one_lt_C_D]) (sub_pos.mpr hδβ)).le
  have hcd₁ := volumeIntegralConstant_one_le D.one_lt_C_D (sub_pos.mpr hδβ)
  have hθ₁ := d.θ₁_pos
  have hθ₂ := d.θ₁_pos.trans_le d.θ₁_le
  have hB : 0 ≤ cancellationBoundaryConstant D.C_D d.θ₁ d.θ₂ := by
    have hCD : 0 ≤ D.C_D := by linarith [D.one_lt_C_D]
    unfold cancellationBoundaryConstant
    exact add_nonneg (mul_nonneg hCD (Real.rpow_nonneg (by positivity) _)) (sq_nonneg _)
  let C := regularizedHolderConstant β δ D.C_D d.θ₁ d.θ₂
  have hCA : cancellationBoundaryConstant D.C_D d.θ₁ d.θ₂ + 7 * volumeIntegralConstant D.C_D δ ≤ C := by
    dsimp [C, regularizedHolderConstant]
    linarith
  have hCS : volumeIntegralConstant D.C_D (β - δ) ≤ C := by dsimp [C, regularizedHolderConstant]; linarith
  have hC₁ : 1 ≤ C := hcd₁.trans hCS
  have hC₁₈ : 18 * volumeIntegralConstant D.C_D δ ≤ C := by dsimp [C, regularizedHolderConstant]; linarith
  have hC : 0 ≤ C := zero_le_one.trans hC₁
  have hsum : 0 ≤ A + S + C_K := add_nonneg (add_nonneg hK.kernel.A_nonneg hK.kernel.S_nonneg) hCan.1
  have hH : 0 ≤ (holderSemi δ G f).toReal := ENNReal.toReal_nonneg
  rcases eq_or_ne x₀ x with rfl | hxx
  · simp only [sub_self, abs_zero, dist_self, Real.zero_rpow hδr.ne', mul_zero, le_refl]
  let t := dist x₀ x
  have ht : 0 < t := dist_pos.mpr hxx
  have htδ := Real.rpow_nonneg ht.le (δ : ℝ)
  by_cases htκ : t < D.κ / 3
  · have he := hK.regularized_small_difference d hCan hδ hδβ hf hx₀ hx hxx htκ
    have he₃ := rpow_scaled_le (c := 3) (by norm_num) ht.le hδ₁
    have he₄ := rpow_scaled_le (c := 4) (by norm_num) ht.le hδ₁
    have h₃ := mul_le_mul_of_nonneg_left he₃ (mul_nonneg (mul_nonneg hK.kernel.A_nonneg hH) hcδ)
    have h₄ := mul_le_mul_of_nonneg_left he₄ (mul_nonneg (mul_nonneg hK.kernel.A_nonneg hH) hcδ)
    have heA := mul_le_mul_of_nonneg_right hCA hK.kernel.A_nonneg
    have heS := mul_le_mul_of_nonneg_right hCS hK.kernel.S_nonneg
    have heK := mul_le_mul_of_nonneg_right hC₁ hCan.1
    have hcoef : volumeIntegralConstant D.C_D (β - δ) * S + C_K +
        cancellationBoundaryConstant D.C_D d.θ₁ d.θ₂ * A + 7 * volumeIntegralConstant D.C_D δ * A ≤ C * (A + S + C_K) := by
      nlinarith
    have hmul := mul_le_mul_of_nonneg_right hcoef (mul_nonneg hH htδ)
    dsimp [t] at h₃ h₄ hmul
    change _ ≤ C * (A + S + C_K) * (holderSemi δ G f).toReal * dist x₀ x ^ (δ : ℝ)
    nlinarith
  · have hr : R ≤ 9 * t := by have htκ' := le_of_not_gt htκ; linarith [hK.radius_le]
    have hp := (Real.rpow_le_rpow hK.radius_pos.le hr hδr.le).trans
      (rpow_scaled_le (c := 9) (by norm_num) ht.le hδ₁)
    have he₀ := hK.regularized_abs_le hδ hf hx₀
    have he₁ := hK.regularized_abs_le hδ hf hx
    simp only [zero_add] at he₀ he₁
    have he := abs_sub (regularizedIntegral D.μ G K f x) (regularizedIntegral D.μ G K f x₀)
    have hpow := mul_le_mul_of_nonneg_left hp (mul_nonneg (mul_nonneg hK.kernel.A_nonneg hH) hcδ)
    have hcoef : 18 * volumeIntegralConstant D.C_D δ * A ≤ C * (A + S + C_K) := by
      have heA := mul_le_mul_of_nonneg_right hC₁₈ hK.kernel.A_nonneg
      have heS := mul_nonneg hC (add_nonneg hK.kernel.S_nonneg hCan.1)
      nlinarith
    have hmul := mul_le_mul_of_nonneg_right hcoef (mul_nonneg hH htδ)
    dsimp [t] at hpow hmul
    change _ ≤ C * (A + S + C_K) * (holderSemi δ G f).toReal * dist x₀ x ^ (δ : ℝ)
    nlinarith

end RothschildStein.H2
