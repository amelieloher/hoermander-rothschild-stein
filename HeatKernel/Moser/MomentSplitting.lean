-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib

/-!
# Splitting small moments at a level

Hölder's inequality controls the part of a small moment above a level by a
larger moment and the measure of the upper level set. This is the integral
splitting used in the reverse Hölder argument of Bombieri and Giusti.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace HeatKernel

/-- On a measurable set, a smaller moment is controlled by a larger moment and its measure. -/
theorem lintegral_rpow_le_moment_mul_measure {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ≥0∞} (hf : AEMeasurable f μ)
    {p p₀ : ℝ} (hp : 0 < p) (hpp₀ : p < p₀) (s : Set α) :
    (∫⁻ x in s, f x ^ p ∂μ) ≤
      (∫⁻ x in s, f x ^ p₀ ∂μ) ^ (p / p₀) * μ s ^ (1 - p / p₀) := by
  have hr : 1 < p₀ / p := (lt_div_iff₀ hp).2 (by simpa)
  have hc := Real.HolderConjugate.conjExponent hr
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ.restrict s) hc (g := fun _ => 1)
    ((hf.mono_measure Measure.restrict_le_self).pow_const p) aemeasurable_const
  have he : p * (p₀ / p) = p₀ := by field_simp
  have he' : 1 / (p₀ / p) = p / p₀ := by field_simp
  have he'' : 1 / Real.conjExponent (p₀ / p) = 1 - p / p₀ := by
    have := hc.inv_add_inv_eq_one
    simp only [← one_div] at this
    rw [he'] at this
    linarith
  simpa only [Pi.mul_apply, mul_one, Pi.one_apply, ENNReal.one_rpow, lintegral_const,
    Measure.restrict_apply_univ, one_mul, ← ENNReal.rpow_mul, he, he', he''] using h

/-- Splitting at a level bounds a small moment by a constant and a Hölder tail term. -/
theorem lintegral_rpow_le_level_add_tail {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ≥0∞} (hf : Measurable f)
    {p p₀ : ℝ} (hp : 0 < p) (hpp₀ : p < p₀)
    {U : Set α} (b : ℝ≥0∞) :
    (∫⁻ x in U, f x ^ p ∂μ) ≤ b ^ p * μ U +
      (∫⁻ x in U, f x ^ p₀ ∂μ) ^ (p / p₀) *
        μ (U ∩ {x | b < f x}) ^ (1 - p / p₀) := by
  let T := {x | b < f x}
  have hT : MeasurableSet T := measurableSet_lt measurable_const hf
  have hsplit := lintegral_add_compl (μ := μ.restrict U) (f := fun x => f x ^ p) hT
  have hlo : (∫⁻ x in Tᶜ, f x ^ p ∂μ.restrict U) ≤ b ^ p * μ U := by
    calc
      _ ≤ ∫⁻ _x in Tᶜ, b ^ p ∂μ.restrict U := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem hT.compl] with x hx
        exact ENNReal.rpow_le_rpow (le_of_not_gt hx) hp.le
      _ = b ^ p * (μ.restrict U) Tᶜ := by simp
      _ ≤ b ^ p * (μ.restrict U) univ :=
        mul_le_mul_right (measure_mono (subset_univ Tᶜ) :
          (μ.restrict U) Tᶜ ≤ (μ.restrict U) univ) _
      _ = b ^ p * μ U := by simp
  have htail := lintegral_rpow_le_moment_mul_measure (μ := μ) hf.aemeasurable hp hpp₀ (U ∩ T)
  have hmono : (∫⁻ x in U ∩ T, f x ^ p₀ ∂μ) ≤ ∫⁻ x in U, f x ^ p₀ ∂μ :=
    lintegral_mono_set inter_subset_left
  rw [Measure.restrict_restrict hT, inter_comm T U] at hsplit
  calc
    _ = (∫⁻ x in U ∩ T, f x ^ p ∂μ) +
        ∫⁻ x in Tᶜ, f x ^ p ∂μ.restrict U := hsplit.symm
    _ ≤ (∫⁻ x in U, f x ^ p₀ ∂μ) ^ (p / p₀) * μ (U ∩ T) ^ (1 - p / p₀) +
        b ^ p * μ U := add_le_add
          (htail.trans (mul_le_mul_left (ENNReal.rpow_le_rpow hmono
            (div_nonneg hp.le (hp.trans hpp₀).le)) _)) hlo
    _ = _ := add_comm _ _

end HeatKernel
