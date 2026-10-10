-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.BombieriGiustiExponentialTails
public import HeatKernel.Moser.BombieriGiustiCylinderMeasures
import Mathlib.Tactic

/-! # Exponential tails on the buffered Harnack iteration cylinders

The two signed logarithmic tails restrict to the earlier and later iteration
cylinders. Their fixed time-length ratios multiply the logarithmic-tail constants
by `57/40` and `113/96`, respectively. The shift is common to both sides.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace HeatKernel

/-- A relative tail on a larger region restricts to a smaller reference set,
with the supplied region-to-reference measure ratio multiplying its constant. -/
theorem measure_inter_tail_le_of_region_measure_comparison
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {V W s : Set α} {B R : ℝ}
    (hVW : V ⊆ W) (hR : 0 ≤ R)
    (hratio : μ W ≤ ENNReal.ofReal R * μ V)
    (htail : μ (W ∩ s) ≤ ENNReal.ofReal B * μ W) :
    μ (V ∩ s) ≤ ENNReal.ofReal (B * R) * μ V := by
  calc
    μ (V ∩ s) ≤ μ (W ∩ s) := measure_mono (inter_subset_inter_left _ hVW)
    _ ≤ ENNReal.ofReal B * μ W := htail
    _ ≤ ENNReal.ofReal B * (ENNReal.ofReal R * μ V) := mul_le_mul' le_rfl hratio
    _ = ENNReal.ofReal (B * R) * μ V := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul' hR]

/-- The two logarithmic-region estimates give exactly the relative exponential
tails required for the earlier solution and later reciprocal iterations. All
remaining analytic estimates are explicit hypotheses; the cylinder inclusions
and measure ratios are discharged. -/
theorem harnack_iteration_exponential_tails_of_logarithmic_region_tails
    {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E]
    (ν : Measure E) [SFinite ν] (x : E) (t : ℝ) {r τ c Aminus Aplus : ℝ}
    {u : ℝ × E → ℝ}
    (hτlower : t - 113 / 64 * r ^ 2 < τ)
    (hτupper : τ < t - 111 / 64 * r ^ 2)
    (hu : ∀ᵐ y ∂volume.prod ν,
      y ∈ harnackEarlierIterationCylinder x t r 1 ∨
        y ∈ harnackLaterIterationCylinder x t r 1 → 0 < u y)
    (hminus : ∀ ℓ : ℝ, 0 < ℓ →
      (volume.prod ν) ((Ioo (t - 225 / 64 * r ^ 2) τ ×ˢ Metric.ball x (5 / 4 * r)) ∩
        {y | c + ℓ < Real.log (u y)}) ≤ ENNReal.ofReal (Aminus / ℓ) *
          (volume.prod ν) (Ioo (t - 225 / 64 * r ^ 2) τ ×ˢ Metric.ball x (5 / 4 * r)))
    (hplus : ∀ ℓ : ℝ, 0 < ℓ →
      (volume.prod ν) ((Ioo τ t ×ˢ Metric.ball x (5 / 4 * r)) ∩
        {y | Real.log (u y) < c - ℓ}) ≤ ENNReal.ofReal (Aplus / ℓ) *
          (volume.prod ν) (Ioo τ t ×ˢ Metric.ball x (5 / 4 * r))) :
    (∀ ℓ : ℝ, 0 < ℓ →
      (volume.prod ν) (harnackEarlierIterationCylinder x t r 1 ∩
        {y | ENNReal.ofReal (Real.exp ℓ) < ENNReal.ofReal (Real.exp (-c) * u y)}) ≤
      ENNReal.ofReal ((Aminus * (57 / 40)) / ℓ) *
        (volume.prod ν) (harnackEarlierIterationCylinder x t r 1)) ∧
    (∀ ℓ : ℝ, 0 < ℓ →
      (volume.prod ν) (harnackLaterIterationCylinder x t r 1 ∩
        {y | ENNReal.ofReal (Real.exp ℓ) < ENNReal.ofReal (Real.exp c / u y)}) ≤
      ENNReal.ofReal ((Aplus * (113 / 96)) / ℓ) *
        (volume.prod ν) (harnackLaterIterationCylinder x t r 1)) := by
  constructor
  · apply measure_exponential_tail_le_of_logarithmic_upper_tail
      (hu.mono fun y hy hyV => hy (Or.inl hyV))
    intro ℓ hℓ
    have h := measure_inter_tail_le_of_region_measure_comparison
      (harnackEarlierIterationCylinder_subset_logarithmic_region x t hτlower)
      (by norm_num : (0 : ℝ) ≤ 57 / 40)
      (measure_earlier_logarithmic_region_le ν x t r τ hτupper) (hminus ℓ hℓ)
    have heq : (Aminus / ℓ) * (57 / 40) = (Aminus * (57 / 40)) / ℓ := by ring
    simpa only [heq] using h
  · apply measure_reciprocal_exponential_tail_le_of_logarithmic_lower_tail
      (hu.mono fun y hy hyV => hy (Or.inr hyV))
    intro ℓ hℓ
    have h := measure_inter_tail_le_of_region_measure_comparison
      (harnackLaterIterationCylinder_subset_logarithmic_region x t hτupper)
      (by norm_num : (0 : ℝ) ≤ 113 / 96)
      (measure_later_logarithmic_region_le ν x t r τ hτlower) (hplus ℓ hℓ)
    have heq : (Aplus / ℓ) * (113 / 96) = (Aplus * (113 / 96)) / ℓ := by ring
    simpa only [heq] using h

end HeatKernel
