-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.FractionalHolderSplit

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal NNReal

namespace RothschildStein.H2

/-- The three explicit contributions to the fractional Hölder seminorm. -/
def fractionalSemiConstant (C κ R α ν : ℝ) : ℝ :=
  volumeIntegralConstant C (ν - α) * (R + κ / 3) ^ (ν - α) +
    volumeIntegralConstant C ν * (3 ^ ν + 4 ^ ν) * (κ / 3) ^ (ν - α) +
    2 * volumeIntegralConstant C ν * R ^ ν * (3 / κ) ^ α

/-- The explicit full Hölder constant for this estimate. -/
def fractionalHolderConstant (C κ R α ν : ℝ) : ℝ :=
  fractionalSemiConstant C κ R α ν + volumeIntegralConstant C ν * R ^ ν

/-- The small-distance power gain used in BB p. 305. -/
theorem rpow_gain_le {t k α ν : ℝ} (ht : 0 < t) (htk : t ≤ k) (hαν : α ≤ ν) :
    t ^ ν ≤ k ^ (ν - α) * t ^ α := by
  have he := Real.rpow_le_rpow ht.le htk (sub_nonneg.mpr hαν)
  have hb := mul_le_mul_of_nonneg_right he (Real.rpow_nonneg ht.le α)
  rw [← Real.rpow_add ht] at hb
  simpa only [sub_add_cancel] using hb

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Pointwise fractional Hölder continuity, including the omitted large
separation case L12. BB Theorem 7.14, p. 305. The bound is linear in A and S. -/
theorem SupportedKernel.fractional_difference_le {D : LocDoubling X} {E G : Set X}
    {β ν A S R : ℝ} {K : X → X → ℝ} (hK : SupportedKernel D E G β ν A S R K)
    {α : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hαν : α < ν)
    {f : X → ℝ} (hf : AEStronglyMeasurable f (D.μ.restrict G))
    {M : ℝ} (hM : 0 ≤ M) (hfb : ∀ᵐ y ∂D.μ.restrict G, |f y| ≤ M)
    {x₀ x : X} (hx₀ : x₀ ∈ E) (hx : x ∈ E) :
    |fractionalIntegral D.μ G K f x₀ - fractionalIntegral D.μ G K f x| ≤
      fractionalSemiConstant D.C_D D.κ R α ν * (A + S) * M * dist x₀ x ^ α := by
  have hν := hα.trans hαν
  have hcν := (volumeIntegralConstant_pos (C := D.C_D) (by linarith [D.one_lt_C_D]) hν).le
  have hcα := (volumeIntegralConstant_pos (C := D.C_D) (by linarith [D.one_lt_C_D]) (sub_pos.mpr hαν)).le
  have hA := hK.kernel.A_nonneg
  have hS := hK.kernel.S_nonneg
  have hk : 0 < D.κ / 3 := div_pos D.κ_pos (by norm_num)
  let B := volumeIntegralConstant D.C_D (ν - α) * (R + D.κ / 3) ^ (ν - α)
  let N := volumeIntegralConstant D.C_D ν * (3 ^ ν + 4 ^ ν) * (D.κ / 3) ^ (ν - α)
  let L := 2 * volumeIntegralConstant D.C_D ν * R ^ ν * (3 / D.κ) ^ α
  have hB : 0 ≤ B := mul_nonneg hcα (Real.rpow_nonneg (by linarith [hK.radius_pos]) _)
  have hN : 0 ≤ N := mul_nonneg (mul_nonneg hcν (add_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (by norm_num) _))) (Real.rpow_nonneg hk.le _)
  have hL : 0 ≤ L := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hcν) (Real.rpow_nonneg hK.radius_pos.le _)) (Real.rpow_nonneg (div_nonneg (by norm_num) D.κ_pos.le) _)
  rcases eq_or_ne x₀ x with rfl | hxx
  · simp only [sub_self, abs_zero, dist_self, Real.zero_rpow hα.ne', mul_zero, le_refl]
  let t := dist x₀ x
  have ht : 0 < t := dist_pos.mpr hxx
  have htα : 0 ≤ t ^ α := Real.rpow_nonneg ht.le _
  have ha : A ≤ A + S := le_add_of_nonneg_right hS
  have hs : S ≤ A + S := le_add_of_nonneg_left hA
  by_cases htκ : t < D.κ / 3
  · have he := hK.fractional_small_difference hα hαβ hαν hf hM hfb hx₀ hx hxx htκ
    have hp := Real.rpow_le_rpow (add_nonneg hK.radius_pos.le ht.le)
      (by linarith : R + t ≤ R + D.κ / 3) (sub_pos.mpr hαν).le
    have hg := rpow_gain_le ht htκ.le hαν.le
    have hfar : S * M * t ^ α * volumeIntegralConstant D.C_D (ν - α) * (R + t) ^ (ν - α) ≤ B * (A + S) * M * t ^ α := by
      calc
        _ ≤ S * M * t ^ α * volumeIntegralConstant D.C_D (ν - α) * (R + D.κ / 3) ^ (ν - α) :=
          mul_le_mul_of_nonneg_left hp (mul_nonneg (mul_nonneg (mul_nonneg hS hM) htα) hcα)
        _ ≤ _ := by dsimp [B]; nlinarith [mul_le_mul_of_nonneg_right hs (mul_nonneg hB (mul_nonneg hM htα))]
    have hnear : A * M * volumeIntegralConstant D.C_D ν * (3 * t) ^ ν +
        A * M * volumeIntegralConstant D.C_D ν * (4 * t) ^ ν ≤ N * (A + S) * M * t ^ α := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) (show 0 ≤ t from ht.le), Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (show 0 ≤ t from ht.le)]
      have he₁ := mul_le_mul_of_nonneg_left hg (mul_nonneg (mul_nonneg (mul_nonneg hA hM) hcν)
        (add_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) ν) (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 4) ν)))
      have he₂ := mul_le_mul_of_nonneg_right ha (mul_nonneg hN (mul_nonneg hM htα))
      dsimp [N] at he₂ ⊢
      nlinarith
    change _ ≤ (B + N + L) * (A + S) * M * t ^ α
    have he' : 0 ≤ L * (A + S) * M * t ^ α := mul_nonneg (mul_nonneg (mul_nonneg hL (add_nonneg hA hS)) hM) htα
    dsimp [t] at hfar hnear he'
    linarith
  · have he₀ := hK.fractional_abs_le hν hf hM hfb hx₀
    have he₁ := hK.fractional_abs_le hν hf hM hfb hx
    have hratio : 1 ≤ (3 / D.κ) * t := by
      have htκ' := le_of_not_gt htκ
      have he : 1 ≤ (3 * t) / D.κ := (le_div_iff₀ D.κ_pos).mpr (by linarith)
      convert he using 1; ring
    have hp : 1 ≤ (3 / D.κ) ^ α * t ^ α := by
      rw [← Real.mul_rpow (div_nonneg (by norm_num) D.κ_pos.le) ht.le]
      simpa only [Real.one_rpow] using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hratio hα.le
    have hb := abs_sub (fractionalIntegral D.μ G K f x₀) (fractionalIntegral D.μ G K f x)
    have he₂ := mul_le_mul_of_nonneg_left hp (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hA) hM)
      (mul_nonneg hcν (Real.rpow_nonneg hK.radius_pos.le ν)))
    have he₃ := mul_le_mul_of_nonneg_right ha (mul_nonneg hL (mul_nonneg hM htα))
    have he₄ : 0 ≤ (B + N) * (A + S) * M * t ^ α := mul_nonneg (mul_nonneg (mul_nonneg (add_nonneg hB hN) (add_nonneg hA hS)) hM) htα
    change _ ≤ (B + N + L) * (A + S) * M * t ^ α
    dsimp [L, t] at he₂ he₃ he₄
    nlinarith

end RothschildStein.H2
