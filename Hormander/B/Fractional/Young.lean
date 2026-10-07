-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.B.Defs
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Integral.MeanInequalities

@[expose] public section

noncomputable section

open MeasureTheory ENNReal
open scoped ENNReal

namespace Hormander.B

/-- Cauchy–Schwarz for a weighted lower integral. -/
theorem sq_lintegral_le {α : Type*} [MeasurableSpace α] (μ : Measure α) (k h : α → ℝ≥0∞)
    (hk : AEMeasurable k μ) (hh : AEMeasurable h μ) :
    (∫⁻ a, k a * h a ∂μ) ^ 2 ≤ (∫⁻ a, k a ∂μ) * ∫⁻ a, k a * h a ^ 2 ∂μ := by
  have hk' : AEMeasurable (fun a => k a ^ (1/2 : ℝ)) μ := hk.pow_const _
  have hkh : AEMeasurable (fun a => k a ^ (1/2 : ℝ) * h a) μ := hk'.mul hh
  have H := ENNReal.lintegral_mul_le_Lp_mul_Lq μ (Real.HolderConjugate.two_two) hk' hkh
  have e1 : ∀ a, k a * h a = k a ^ (1/2 : ℝ) * (k a ^ (1/2 : ℝ) * h a) := by
    intro a
    rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  have e2 : ∀ a, (k a ^ (1/2 : ℝ)) ^ (2:ℝ) = k a := by
    intro a; rw [← ENNReal.rpow_mul]; norm_num
  have e3 : ∀ a, (k a ^ (1/2 : ℝ) * h a) ^ (2:ℝ) = k a * h a ^ 2 := by
    intro a
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), e2]
    norm_cast
  simp only [Pi.mul_apply, e2, e3] at H
  have : ∫⁻ a, k a * h a ∂μ = ∫⁻ a, k a ^ (1/2 : ℝ) * (k a ^ (1/2 : ℝ) * h a) ∂μ :=
    lintegral_congr (fun a => e1 a)
  rw [this]
  calc _ ≤ ((∫⁻ a, k a ∂μ) ^ (1 / (2:ℝ)) * (∫⁻ a, k a * h a ^ 2 ∂μ) ^ (1 / (2:ℝ))) ^ 2 := by
        gcongr
    _ = _ := by
      have sq : ∀ x : ℝ≥0∞, (x ^ (1 / (2:ℝ))) ^ 2 = x := by
        intro x; rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
      rw [mul_pow, sq, sq]

/-- (Young step) Young's inequality for an integrable kernel acting on a square-integrable function, in
lower-integral form. -/
theorem young_lintegral_sq {N : ℕ} (k f : Carrier N → ℝ≥0∞) (hk : Measurable k)
    (hf : Measurable f) (hK : ∫⁻ a, k a ≠ ⊤) :
    ∫⁻ ξ, (∫⁻ a, k a * f (ξ - a)) ^ 2 ≤ (∫⁻ a, k a) ^ 2 * ∫⁻ ξ, f ξ ^ 2 := by
  have hshift : ∀ ξ : Carrier N, Measurable fun a => f (ξ - a) :=
    fun ξ => hf.comp (measurable_const.sub measurable_id)
  have hpair : Measurable fun p : Carrier N × Carrier N => k p.2 * f (p.1 - p.2) ^ 2 :=
    (hk.comp measurable_snd).mul ((hf.comp (measurable_fst.sub measurable_snd)).pow_const 2)
  calc ∫⁻ ξ, (∫⁻ a, k a * f (ξ - a)) ^ 2
      ≤ ∫⁻ ξ, (∫⁻ a, k a) * ∫⁻ a, k a * f (ξ - a) ^ 2 :=
        lintegral_mono fun ξ => sq_lintegral_le volume k _ hk.aemeasurable
          (hshift ξ).aemeasurable
    _ = (∫⁻ a, k a) * ∫⁻ ξ, ∫⁻ a, k a * f (ξ - a) ^ 2 :=
        lintegral_const_mul' _ _ hK
    _ = (∫⁻ a, k a) * ∫⁻ a, ∫⁻ ξ, k a * f (ξ - a) ^ 2 := by
        rw [lintegral_lintegral_swap hpair.aemeasurable]
    _ = (∫⁻ a, k a) * ∫⁻ a, k a * ∫⁻ ξ, f ξ ^ 2 := by
        congr 1
        refine lintegral_congr fun a => ?_
        have hm : Measurable fun ξ : Carrier N => f (ξ - a) ^ 2 :=
          (hf.comp (measurable_id.sub measurable_const)).pow_const 2
        rw [lintegral_const_mul _ hm]
        congr 1
        exact lintegral_sub_right_eq_self (fun ξ => f ξ ^ 2) a
    _ = _ := by
        rw [lintegral_mul_const _ hk, sq]
        ring

/-- A pointwise convolution bound transfers to the squared lower integrals. -/
theorem young_dominated {N : ℕ} (k f G : Carrier N → ℝ≥0∞) (hk : Measurable k)
    (hf : Measurable f) (hK : ∫⁻ a, k a ≠ ⊤)
    (hG : ∀ ξ, G ξ ≤ ∫⁻ a, k a * f (ξ - a)) :
    ∫⁻ ξ, G ξ ^ 2 ≤ (∫⁻ a, k a) ^ 2 * ∫⁻ ξ, f ξ ^ 2 :=
  (lintegral_mono fun ξ => pow_le_pow_left' (hG ξ) 2).trans (young_lintegral_sq k f hk hf hK)

/-- The kernel convolution of a measurable function is measurable. -/
theorem measurable_kernelConv {N : ℕ} (k f : Carrier N → ℝ≥0∞) (hk : Measurable k)
    (hf : Measurable f) : Measurable fun ξ : Carrier N => ∫⁻ a, k a * f (ξ - a) := by
  have : Measurable fun p : Carrier N × Carrier N => k p.2 * f (p.1 - p.2) :=
    (hk.comp measurable_snd).mul (hf.comp (measurable_fst.sub measurable_snd))
  exact this.lintegral_prod_right'

end Hormander.B
