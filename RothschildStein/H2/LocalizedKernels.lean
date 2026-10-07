-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.LocalizationBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Metric
open scoped NNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

private theorem product_bound {c k b Λ t H : ℝ} (hc : |c| ≤ Λ * t)
    (hk : |k| ≤ H) (hb : 0 ≤ b) (hb₁ : b ≤ 1) :
    |c * k * b| ≤ Λ * H * t := by
  have hΛt : 0 ≤ Λ * t := (abs_nonneg c).trans hc
  have hH : 0 ≤ H := (abs_nonneg k).trans hk
  rw [abs_mul, abs_mul, abs_of_nonneg hb]
  calc
    _ ≤ (Λ * t) * H * 1 := mul_le_mul
      (mul_le_mul hc hk (abs_nonneg _) hΛt) hb₁ hb (mul_nonneg hΛt hH)
    _ = _ := by ring

/-- (ii) Localization on a doubling patch preserves the size constant
and gives S + 4RLₐ C_D²(3/2)^ν A. BB Proposition 7.11, pp. 299–301. -/
theorem localized_kernelClass_on_patch (P : DoublingPatch X) (hPS : MeasurableSet P.S)
    {z : X} {R : ℝ} (hR : 0 < R) (hRρ : R ≤ P.ρ) (_hUS : ball z R ⊆ P.S)
    {a b : X → ℝ} {Lₐ Lᵦ : ℝ≥0} {K : X → X → ℝ} {β ν A S : ℝ}
    (ha : KernelCutoff (ball z R) Lₐ a) (hb : KernelCutoff (ball z R) Lᵦ b)
    (hK : KernelClass P.μ (ball z R) β ν A S K) :
    KernelClass P.μ P.S β ν A
      (S + 4 * R * (Lₐ : ℝ) * P.C_D ^ 2 * (3 / 2 : ℝ) ^ ν * A)
      (localizedKernel (ball z R) a b K) := by
  classical
  let q := (3 / 2 : ℝ) ^ ν * P.C_D ^ 2
  let Λ := 4 * R * (Lₐ : ℝ)
  have hq : 1 ≤ q := by
    have hp : 1 ≤ (3 / 2 : ℝ) ^ ν := Real.one_le_rpow (by norm_num) hK.ν_nonneg
    have hc : 1 ≤ P.C_D ^ 2 := by nlinarith [P.one_lt_C_D, sq_nonneg (P.C_D - 1)]
    dsimp [q]
    nlinarith
  have hqn : 0 ≤ q := by linarith
  have hΛ : 0 ≤ Λ := by dsimp [Λ]; positivity
  have hE : 0 ≤ Λ * q * A := mul_nonneg (mul_nonneg hΛ hqn) hK.A_nonneg
  have hconst : S + 4 * R * (Lₐ : ℝ) * P.C_D ^ 2 * (3 / 2 : ℝ) ^ ν * A = S + Λ * q * A := by
    dsimp [Λ, q]; ring
  rw [hconst]
  refine ⟨hPS, (measurable_localizedKernel isOpen_ball.measurableSet ha hb hK.measurable).comp
    ((measurable_subtype_coe.comp measurable_fst).prodMk
      (measurable_subtype_coe.comp measurable_snd)), hK.β_pos, hK.β_le_one, hK.ν_nonneg,
    hK.A_nonneg, add_nonneg hK.S_nonneg hE, ?_, ?_⟩
  · intro x _ y _ hxy
    exact localizedKernel_size ha hb hK hxy
  · intro x₀ hx₀ x hx y hy hsep
    have hd₀ : 0 < dist x₀ y := by have := dist_nonneg (x := x₀) (y := x); linarith
    have hd : 0 < dist x y := by have := (distance_comparison hsep).2; linarith
    let w := kernelWeight P.μ ν x₀ y
    let t := (dist x₀ x / dist x₀ y) ^ β
    have hw : 0 ≤ w := kernelWeight_nonneg _ _ _ _
    have ht : 0 ≤ t := Real.rpow_nonneg (by positivity) _
    have hCw : 0 ≤ (S + Λ * q * A) * w * t :=
      mul_nonneg (mul_nonneg (add_nonneg hK.S_nonneg hE) hw) ht
    by_cases hyU : y ∈ ball z R
    swap
    · simpa only [localizedKernel, and_false, hyU, ite_false, sub_self, abs_zero] using hCw
    by_cases hx₀U : x₀ ∈ ball z R
    · by_cases hxU : x ∈ ball z R
      · have hrad : dist x₀ y ≤ 4 * R := by
          have := dist_lt_two_radius hx₀U hyU; linarith
        have hvar : |a x₀ - a x| ≤ Λ * t :=
          lipschitz_variation_ratio ha.lipschitz hK.β_pos hK.β_le_one hsep hrad
        have hweight : kernelWeight P.μ ν x y ≤ q * w :=
          P.kernelWeight_compare hK.ν_nonneg hx₀ hx hsep (by linarith)
        have hk : |K x y| ≤ A * q * w :=
          (hK.size x hxU y hyU (dist_pos.mp hd)).trans (by
            have he := mul_le_mul_of_nonneg_left hweight hK.A_nonneg
            dsimp [w] at he ⊢; nlinarith)
        have hsecond := product_bound hvar hk (hb.nonneg y) (hb.le_one y)
        have hfirst : |a x₀ * (K x₀ y - K x y) * b y| ≤ S * w * t :=
          (cutoff_product_abs_le (ha.nonneg x₀) (ha.le_one x₀) (hb.nonneg y) (hb.le_one y)).trans
            (hK.smooth x₀ hx₀U x hxU y hyU hsep)
        have hid : a x₀ * K x₀ y * b y - a x * K x y * b y =
            a x₀ * (K x₀ y - K x y) * b y + (a x₀ - a x) * K x y * b y := by ring
        simp only [localizedKernel, hx₀U, hxU, hyU, and_self, ite_eq_left]
        rw [hid]
        calc
          _ ≤ |a x₀ * (K x₀ y - K x y) * b y| + |(a x₀ - a x) * K x y * b y| := abs_add_le _ _
          _ ≤ S * w * t + Λ * (A * q * w) * t := add_le_add hfirst hsecond
          _ = _ := by ring
      · have hrad : dist x₀ y ≤ 4 * R := by
          have := dist_lt_two_radius hx₀U hyU; linarith
        have hvar : |a x₀| ≤ Λ * t := by
          simpa only [ha.outside x hxU, sub_zero] using
            lipschitz_variation_ratio ha.lipschitz hK.β_pos hK.β_le_one hsep hrad
        have hk : |K x₀ y| ≤ A * q * w :=
          (hK.size x₀ hx₀U y hyU (dist_pos.mp hd₀)).trans (by
            have he := mul_le_mul_of_nonneg_left hq (mul_nonneg hK.A_nonneg hw)
            nlinarith)
        have he := product_bound hvar hk (hb.nonneg y) (hb.le_one y)
        simp only [localizedKernel, hx₀U, hxU, hyU, and_self, false_and, ite_eq_left,
          ite_false, sub_zero]
        calc
          _ ≤ Λ * (A * q * w) * t := he
          _ ≤ (S + Λ * q * A) * w * t := by
            have := mul_nonneg (mul_nonneg hK.S_nonneg hw) ht
            nlinarith
    · by_cases hxU : x ∈ ball z R
      · have hrad : dist x₀ y ≤ 4 * R := by
          have := dist_lt_two_radius hxU hyU
          have := (distance_comparison hsep).2
          linarith
        have hvar : |a x| ≤ Λ * t := by
          simpa only [ha.outside x₀ hx₀U, zero_sub, abs_neg] using
            lipschitz_variation_ratio ha.lipschitz hK.β_pos hK.β_le_one hsep hrad
        have hweight : kernelWeight P.μ ν x y ≤ q * w :=
          P.kernelWeight_compare hK.ν_nonneg hx₀ hx hsep (by linarith)
        have hk : |K x y| ≤ A * q * w :=
          (hK.size x hxU y hyU (dist_pos.mp hd)).trans (by
            have he := mul_le_mul_of_nonneg_left hweight hK.A_nonneg
            dsimp [w] at he ⊢; nlinarith)
        have he := product_bound hvar hk (hb.nonneg y) (hb.le_one y)
        simp only [localizedKernel, hx₀U, hxU, hyU, and_self, false_and, ite_eq_left,
          ite_false, zero_sub, abs_neg]
        calc
          _ ≤ Λ * (A * q * w) * t := he
          _ ≤ (S + Λ * q * A) * w * t := by
            have := mul_nonneg (mul_nonneg hK.S_nonneg hw) ht
            nlinarith
      · simpa only [localizedKernel, hx₀U, hxU, false_and, ite_false, sub_self, abs_zero] using hCw

end RothschildStein.H2
