-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueCutoffMoments
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-! # Nested norm steps from localized positive-power moments -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace HeatKernel

/-- A unit cutoff supported in a measurable region bounds its full power moment
by the original power moment restricted to that region. -/
theorem lintegral_supported_cutoff_power_le {α : Type*} [TopologicalSpace α]
    [MeasurableSpace α] (μ : Measure α) {V : Set α} (hV : MeasurableSet V)
    (u φ : α → ℝ) (hφ : ∀ x, φ x ∈ Icc (0 : ℝ) 1)
    (hs : tsupport φ ⊆ V) {p : ℝ} (hp : 0 < p) :
    (∫⁻ x, ‖u x * φ x‖ₑ ^ p ∂μ) ≤ ∫⁻ x in V, ‖u x‖ₑ ^ p ∂μ := by
  rw [← lintegral_indicator hV]
  apply lintegral_mono
  intro x
  by_cases hx : x ∈ V
  · rw [indicator_of_mem hx]
    have hφe : ‖φ x‖ₑ ≤ 1 := by
      rw [Real.enorm_of_nonneg (hφ x).1]
      exact (ENNReal.ofReal_le_ofReal (hφ x).2).trans_eq (by simp)
    apply ENNReal.rpow_le_rpow ?_ hp.le
    rw [enorm_mul]
    simpa only [mul_one] using mul_le_mul' le_rfl hφe
  · have hz : φ x = 0 := by
      by_contra hn
      exact hx (hs (subset_tsupport φ (Function.mem_support.mpr hn)))
    simp only [hz, mul_zero, enorm_zero, ENNReal.zero_rpow_of_pos hp, indicator_of_notMem hx,
      le_refl]

/-- Uniform truncated half-power moment bounds give the full nested norm step
by Fatou. Measurability is required only on the two actual product cylinders. -/
theorem eLpNorm_step_le_of_uniform_linearTail_power_moments {N : ℕ}
    {a a' b p ν : ℝ} (haa' : a ≤ a') (hp : 2 ≤ p) (hν : 2 < ν)
    {V S : Set (Fin N → ℝ)} (hV : MeasurableSet V)
    (u : ℝ → (Fin N → ℝ) → ℝ) (θ : ℝ → ℝ) (η φ : (Fin N → ℝ) → ℝ)
    (hφ : ∀ x, φ x ∈ Icc (0 : ℝ) 1) (hs : tsupport φ ⊆ V)
    (hu0 : ∀ᵐ t ∂volume.restrict (Icc a b), ∀ᵐ x ∂volume, η x ≠ 0 → 0 ≤ u t x)
    (hplateau : ∀ᵐ t ∂volume.restrict (Icc a' b),
      ∀ᵐ x ∂volume.restrict S, θ t * η x = 1)
    (hi : AEStronglyMeasurable (fun z : ℝ × (Fin N → ℝ) => u z.1 z.2)
      ((volume.restrict (Icc a' b)).prod (volume.restrict S)))
    (ho : AEStronglyMeasurable (fun z : ℝ × (Fin N → ℝ) => u z.1 z.2)
      ((volume.restrict (Icc a b)).prod (volume.restrict V)))
    {A D : ℝ≥0∞}
    (hMoment : ∀ M : ℝ, 0 < M → (∫⁻ t in Icc a b, ∫⁻ x,
      ‖θ t * η x * linearTailPositivePower M (p / 2) (u t x)‖ₑ ^
        (2 + 4 / ν) ∂volume) ≤
          A * (D * (∫⁻ t in Icc a b, ∫⁻ x, ‖u t x * φ x‖ₑ ^ p ∂volume)) ^
            (1 + 2 / ν)) :
    eLpNorm (fun z : ℝ × (Fin N → ℝ) => u z.1 z.2)
      (ENNReal.ofReal (p * (1 + 2 / ν)))
      ((volume.restrict (Icc a' b)).prod (volume.restrict S)) ≤
        A ^ (1 / (p * (1 + 2 / ν))) * D ^ (1 / p) *
          eLpNorm (fun z : ℝ × (Fin N → ℝ) => u z.1 z.2) (ENNReal.ofReal p)
            ((volume.restrict (Icc a b)).prod (volume.restrict V)) := by
  have hp0 : 0 < p := by linarith
  have hν0 : 0 < ν := by linarith
  have hγ : 1 ≤ p * (1 + 2 / ν) := by
    nlinarith [div_pos (by norm_num : (0 : ℝ) < 2) hν0]
  have hτ : (volume : Measure ℝ).restrict (Icc a' b) ≤ volume.restrict (Icc a b) :=
    Measure.restrict_mono (Icc_subset_Icc_left haa') le_rfl
  have hbound := lintegral_rpow_le_of_boundedPositivePower_bounds _ hi.norm.aemeasurable
    (Filter.Eventually.of_forall fun z => norm_nonneg (u z.1 z.2)) hγ (fun n => by
      have hc := lintegral_prod_bounded_power_le_linearTail_cutoff_moment hτ
        (Measure.restrict_le_self : (volume : Measure (Fin N → ℝ)).restrict S ≤ volume)
        u (fun t x => θ t * η x) (M := (n : ℝ) + 1) (by positivity) hp hν hi hplateau
      have he : (∫⁻ t in Icc a b, ∫⁻ x,
          ‖linearTailPositivePower ((n : ℝ) + 1) (p / 2) ‖u t x‖ * (θ t * η x)‖ₑ ^
            (2 + 4 / ν) ∂volume) =
          ∫⁻ t in Icc a b, ∫⁻ x,
            ‖θ t * η x * linearTailPositivePower ((n : ℝ) + 1) (p / 2) (u t x)‖ₑ ^
              (2 + 4 / ν) ∂volume := by
        apply lintegral_congr_ae
        filter_upwards [hu0] with t ht
        apply lintegral_congr_ae
        filter_upwards [ht] with x hx
        by_cases hη : η x = 0
        · simp only [hη, mul_zero, zero_mul]
        · rw [Real.norm_of_nonneg (hx hη)]
          congr 2
          ring
      rw [he] at hc
      exact hc.trans (hMoment _ (by positivity)))
  have he (z : ℝ × (Fin N → ℝ)) :
      ENNReal.ofReal (‖u z.1 z.2‖ ^ (p * (1 + 2 / ν))) =
        ‖u z.1 z.2‖ₑ ^ (p * (1 + 2 / ν)) := by
    rw [← enorm_norm, Real.enorm_of_nonneg (norm_nonneg _),
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (zero_le_one.trans hγ)]
  simp_rw [he] at hbound
  have hinput : (∫⁻ t in Icc a b, ∫⁻ x, ‖u t x * φ x‖ₑ ^ p ∂volume) ≤
      ∫⁻ z : ℝ × (Fin N → ℝ), ‖u z.1 z.2‖ₑ ^ p
        ∂(volume.restrict (Icc a b)).prod (volume.restrict V) := by
    rw [lintegral_prod _ (ho.enorm.pow_const p)]
    exact lintegral_mono fun t => lintegral_supported_cutoff_power_le volume hV (u t) φ hφ hs hp0
  apply eLpNorm_step_le_of_parabolic_moment_bound _ _ hp0 (by positivity) hi ho
  exact hbound.trans (mul_le_mul' le_rfl
    (ENNReal.rpow_le_rpow (mul_le_mul' le_rfl hinput) (by positivity)))

end HeatKernel
