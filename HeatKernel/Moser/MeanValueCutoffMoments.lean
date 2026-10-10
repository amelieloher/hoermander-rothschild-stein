-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueEnergyNorm
public import HeatKernel.Moser.MeanValueLinearTailPowers
import Mathlib.Tactic

/-! # Inner moments controlled by a power cutoff -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory
open scoped ENNReal
namespace HeatKernel

/-- A cutoff equal to one on the inner region preserves the higher moment of the
power transform there; enlarging the two measures gives the cutoff moment bound. -/
theorem lintegral_power_le_cutoff_power_moment
    {T α : Type*} [MeasurableSpace T] [MeasurableSpace α]
    {τinner τouter : Measure T} {μinner μouter : Measure α}
    (hτ : τinner ≤ τouter) (hμ : μinner ≤ μouter)
    (u η : T → α → ℝ) {p ν : ℝ} (hp : 0 ≤ p)
    (hη : ∀ᵐ t ∂τinner, ∀ᵐ x ∂μinner, η t x = 1) :
    (∫⁻ t, ∫⁻ x, ‖u t x‖ₑ ^ (p * (1 + 2 / ν)) ∂μinner ∂τinner) ≤
      (∫⁻ t, ∫⁻ x, ‖‖u t x‖ ^ (p / 2) * η t x‖ₑ ^ (2 + 4 / ν)
        ∂μouter ∂τouter) := by
  have he : p / 2 * (2 + 4 / ν) = p * (1 + 2 / ν) := by ring
  calc
    _ = ∫⁻ t, ∫⁻ x, ‖‖u t x‖ ^ (p / 2) * η t x‖ₑ ^ (2 + 4 / ν)
        ∂μinner ∂τinner := by
      apply lintegral_congr_ae
      filter_upwards [hη] with t ht
      apply lintegral_congr_ae
      filter_upwards [ht] with x hx
      rw [hx, mul_one, Real.enorm_rpow_of_nonneg (norm_nonneg _) (by positivity),
        enorm_norm, ← ENNReal.rpow_mul, he]
    _ ≤ ∫⁻ t, ∫⁻ x, ‖‖u t x‖ ^ (p / 2) * η t x‖ₑ ^ (2 + 4 / ν)
        ∂μouter ∂τinner := lintegral_mono fun _ => lintegral_mono' hμ le_rfl
    _ ≤ _ := lintegral_mono' hτ le_rfl

/-- The same cutoff comparison for the actual inner spacetime product measure. -/
theorem lintegral_prod_power_le_cutoff_power_moment
    {T α : Type*} [MeasurableSpace T] [MeasurableSpace α]
    {τinner τouter : Measure T} {μinner μouter : Measure α} [SFinite μinner]
    (hτ : τinner ≤ τouter) (hμ : μinner ≤ μouter)
    (u η : T → α → ℝ) {p ν : ℝ} (hp : 0 ≤ p)
    (hu : AEStronglyMeasurable (fun z : T × α => u z.1 z.2) (τinner.prod μinner))
    (hη : ∀ᵐ t ∂τinner, ∀ᵐ x ∂μinner, η t x = 1) :
    (∫⁻ z, ‖u z.1 z.2‖ₑ ^ (p * (1 + 2 / ν)) ∂τinner.prod μinner) ≤
      (∫⁻ t, ∫⁻ x, ‖‖u t x‖ ^ (p / 2) * η t x‖ₑ ^ (2 + 4 / ν)
        ∂μouter ∂τouter) := by
  rw [lintegral_prod _ (hu.enorm.pow_const _)]
  exact lintegral_power_le_cutoff_power_moment hτ hμ u η hp hη

/-- A cutoff equal to one on the inner region controls the clipped higher moment
by the corresponding linear-tail half-power moment, uniformly in the truncation. -/
theorem lintegral_bounded_power_le_linearTail_cutoff_moment
    {T α : Type*} [MeasurableSpace T] [MeasurableSpace α]
    {τinner τouter : Measure T} {μinner μouter : Measure α}
    (hτ : τinner ≤ τouter) (hμ : μinner ≤ μouter)
    (u η : T → α → ℝ) {M p ν : ℝ} (hM : 0 ≤ M) (hν : 2 < ν)
    (hη : ∀ᵐ t ∂τinner, ∀ᵐ x ∂μinner, η t x = 1) :
    (∫⁻ t, ∫⁻ x, ENNReal.ofReal
      (boundedPositivePower M (p * (1 + 2 / ν)) ‖u t x‖) ∂μinner ∂τinner) ≤
    ∫⁻ t, ∫⁻ x, ‖linearTailPositivePower M (p / 2) ‖u t x‖ * η t x‖ₑ ^
      (2 + 4 / ν) ∂μouter ∂τouter := by
  have hνpos : 0 < ν := by linarith
  have hr : 0 ≤ 2 + 4 / ν := by positivity
  have hpoint (s : ℝ) : ENNReal.ofReal (boundedPositivePower M (p * (1 + 2 / ν)) s) ≤
      ‖linearTailPositivePower M (p / 2) s‖ₑ ^ (2 + 4 / ν) := by
    have hm : 0 ≤ min M (max 0 s) := le_min hM (le_max_left _ _)
    have hb : 0 ≤ boundedPositivePower M (p / 2) s := Real.rpow_nonneg hm _
    have hl : boundedPositivePower M (p / 2) s ≤ linearTailPositivePower M (p / 2) s :=
      le_add_of_nonneg_right (mul_nonneg (Real.rpow_nonneg hM _) (le_max_left _ _))
    have he : boundedPositivePower M (p * (1 + 2 / ν)) s =
        (boundedPositivePower M (p / 2) s) ^ (2 + 4 / ν) := by
      unfold boundedPositivePower
      rw [← Real.rpow_mul hm]
      congr 1
      ring
    rw [he, ← Real.enorm_rpow_of_nonneg (hb.trans hl) hr,
      Real.enorm_of_nonneg (Real.rpow_nonneg (hb.trans hl) _)]
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hb hl hr)
  calc
    _ ≤ ∫⁻ t, ∫⁻ x, ‖linearTailPositivePower M (p / 2) ‖u t x‖ * η t x‖ₑ ^
        (2 + 4 / ν) ∂μinner ∂τinner := by
      apply lintegral_mono_ae
      filter_upwards [hη] with t ht
      apply lintegral_mono_ae
      filter_upwards [ht] with x hx
      simpa only [hx, mul_one] using hpoint ‖u t x‖
    _ ≤ ∫⁻ t, ∫⁻ x, ‖linearTailPositivePower M (p / 2) ‖u t x‖ * η t x‖ₑ ^
        (2 + 4 / ν) ∂μouter ∂τinner := lintegral_mono fun _ => lintegral_mono' hμ le_rfl
    _ ≤ _ := lintegral_mono' hτ le_rfl

/-- For the actual spacetime product measure, the clipped higher moment is
controlled by the linear-tail half-power cutoff. Only the plateau and measure
inclusions are geometric inputs; no higher-moment finiteness is assumed. -/
theorem lintegral_prod_bounded_power_le_linearTail_cutoff_moment
    {T α : Type*} [MeasurableSpace T] [MeasurableSpace α]
    {τinner τouter : Measure T} {μinner μouter : Measure α} [SFinite μinner]
    (hτ : τinner ≤ τouter) (hμ : μinner ≤ μouter)
    (u η : T → α → ℝ) {M p ν : ℝ} (hM : 0 ≤ M) (hp : 2 ≤ p) (hν : 2 < ν)
    (hu : AEStronglyMeasurable (fun z : T × α => u z.1 z.2) (τinner.prod μinner))
    (hη : ∀ᵐ t ∂τinner, ∀ᵐ x ∂μinner, η t x = 1) :
    (∫⁻ z, ENNReal.ofReal
      (boundedPositivePower M (p * (1 + 2 / ν)) ‖u z.1 z.2‖) ∂τinner.prod μinner) ≤
      ∫⁻ t, ∫⁻ x, ‖linearTailPositivePower M (p / 2) ‖u t x‖ * η t x‖ₑ ^
        (2 + 4 / ν) ∂μouter ∂τouter := by
  have hγ : 1 ≤ p * (1 + 2 / ν) := by
    have hνpos : 0 < ν := by linarith
    have hd : 0 < 2 / ν := div_pos (by norm_num) hνpos
    nlinarith
  have hm : AEMeasurable (fun z : T × α => ENNReal.ofReal
      (boundedPositivePower M (p * (1 + 2 / ν)) ‖u z.1 z.2‖)) (τinner.prod μinner) := by
    simpa only [Function.comp_def] using
      ((lipschitzWith_boundedPositivePower hM hγ).continuous.aemeasurable.comp_aemeasurable
        hu.norm.aemeasurable).ennreal_ofReal
  rw [lintegral_prod _ hm]
  exact lintegral_bounded_power_le_linearTail_cutoff_moment hτ hμ u η hM hν hη

end HeatKernel
