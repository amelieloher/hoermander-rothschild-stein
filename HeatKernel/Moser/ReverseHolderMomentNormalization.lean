-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.ReverseHolderReferenceNorms
import Mathlib.Tactic

/-! The moment form of reverse-Hölder bounds with one reference mass. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace HeatKernel

/-- Undoing the common reference normalization yields the moment estimate
with the mass raised to the difference of the two reciprocal exponents. -/
theorem reverse_holder_normalized_norm_bound_to_moments
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (S T : Set α)
    {u : α → ℝ} {c p p₀ A : ℝ} {m : ℝ≥0∞}
    (hu : Measurable u) (hc : 0 < c) (hp : 0 < p) (hp₀ : 0 < p₀)
    (hpp₀ : p ≤ p₀) (hA : 0 ≤ A) (hm : m ≠ 0) (hmtop : m ≠ ⊤)
    (hu0 : ∀ᵐ z ∂μ.restrict S, 0 ≤ u z)
    (hu0' : ∀ᵐ z ∂μ.restrict T, 0 ≤ u z)
    (h : eLpNorm (fun z => u z + c) (ENNReal.ofReal p₀) (m⁻¹ • μ.restrict S) ≤
      ENNReal.ofReal (A ^ (1 / p - 1 / p₀)) *
        eLpNorm (fun z => u z + c) (ENNReal.ofReal p) (m⁻¹ • μ.restrict T)) :
    (∫⁻ z in S, ENNReal.ofReal (u z + c) ^ p₀ ∂μ) ^ (1 / p₀) ≤
      (ENNReal.ofReal A * m⁻¹) ^ (1 / p - 1 / p₀) *
        (∫⁻ z in T, ENNReal.ofReal (u z + c) ^ p ∂μ) ^ (1 / p) := by
  have hd : 0 ≤ 1 / p - 1 / p₀ :=
    sub_nonneg.mpr (one_div_le_one_div_of_le hp hpp₀)
  have hcancel : m ^ (1 / p₀) * m⁻¹ ^ (1 / p₀) = 1 := by
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
      ENNReal.mul_inv_cancel hm hmtop, ENNReal.one_rpow]
  have hmass : m ^ (1 / p₀) * m⁻¹ ^ (1 / p) = m⁻¹ ^ (1 / p - 1 / p₀) := by
    rw [ENNReal.inv_rpow, ← ENNReal.rpow_neg,
      ← ENNReal.rpow_add _ _ hm hmtop,
      show 1 / p₀ + -(1 / p) = -(1 / p - 1 / p₀) by ring,
      ENNReal.rpow_neg, ENNReal.inv_rpow]
  have hfactor : m ^ (1 / p₀) * ENNReal.ofReal (A ^ (1 / p - 1 / p₀)) *
      m⁻¹ ^ (1 / p) = (ENNReal.ofReal A * m⁻¹) ^ (1 / p - 1 / p₀) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg hA hd,
      ENNReal.mul_rpow_of_nonneg _ _ hd]
    calc
      _ = ENNReal.ofReal A ^ (1 / p - 1 / p₀) *
          (m ^ (1 / p₀) * m⁻¹ ^ (1 / p)) := by ac_rfl
      _ = _ := by rw [hmass]
  rw [eLpNorm_smul_measure_of_ne_zero_of_ne_top (ENNReal.ofReal_pos.mpr hp₀).ne'
    ENNReal.ofReal_ne_top,
    eLpNorm_smul_measure_of_ne_zero_of_ne_top (ENNReal.ofReal_pos.mpr hp).ne'
      ENNReal.ofReal_ne_top] at h
  simp only [one_div, ENNReal.toReal_inv, ENNReal.toReal_ofReal hp₀.le,
    ENNReal.toReal_ofReal hp.le, smul_eq_mul] at h
  have hnorm : eLpNorm (fun z => u z + c) (ENNReal.ofReal p₀) (μ.restrict S) ≤
      (ENNReal.ofReal A * m⁻¹) ^ (1 / p - 1 / p₀) *
        eLpNorm (fun z => u z + c) (ENNReal.ofReal p) (μ.restrict T) := by
    calc
      _ = m ^ (1 / p₀) * (m⁻¹ ^ (1 / p₀) *
          eLpNorm (fun z => u z + c) (ENNReal.ofReal p₀) (μ.restrict S)) := by
        rw [← mul_assoc, hcancel, one_mul]
      _ ≤ m ^ (1 / p₀) * (ENNReal.ofReal (A ^ (1 / p - 1 / p₀)) *
          (m⁻¹ ^ (1 / p) * eLpNorm (fun z => u z + c) (ENNReal.ofReal p) (μ.restrict T))) :=
        mul_le_mul' le_rfl (by simpa only [one_div] using h)
      _ = (m ^ (1 / p₀) * ENNReal.ofReal (A ^ (1 / p - 1 / p₀)) * m⁻¹ ^ (1 / p)) *
          eLpNorm (fun z => u z + c) (ENNReal.ofReal p) (μ.restrict T) := by ac_rfl
      _ = _ := by rw [hfactor]
  have heq (V : Set α) (q : ℝ) (hq : 0 < q) (hpos : ∀ᵐ z ∂μ.restrict V, 0 ≤ u z) :
      eLpNorm (fun z => u z + c) (ENNReal.ofReal q) (μ.restrict V) =
        (∫⁻ z in V, ENNReal.ofReal (u z + c) ^ q ∂μ) ^ (1 / q) := by
    have hf : Measurable (fun z => u z + c) := hu.add measurable_const
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (f := fun z => u z + c)
      (ENNReal.ofReal_pos.mpr hq).ne' ENNReal.ofReal_ne_top hf.aestronglyMeasurable,
      ENNReal.toReal_ofReal hq.le]
    congr 1
    apply lintegral_congr_ae
    filter_upwards [hpos] with z hz
    rw [Real.enorm_of_nonneg (add_nonneg hz hc.le)]
  rwa [heq S p₀ hp₀ hu0, heq T p hp hu0'] at hnorm

end HeatKernel
