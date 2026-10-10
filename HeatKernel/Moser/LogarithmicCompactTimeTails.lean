-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.LogarithmicSeparatingTimeTail
import Mathlib.Tactic
import all Mathlib.Basic.Real.Basic

/-! # Both logarithmic tails inside a compact time interval -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
namespace HeatKernel

/-- One compact-time variance and mean-energy estimate supplies both tails at
every separating time in that compact interval. -/
theorem measureReal_logarithmic_compact_time_tails_le
    {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν]
    {w f : ℝ → X → ℝ} {m E : ℝ → ℝ} {a b τ C K : ℝ} {I : Set ℝ}
    (ha : a ≤ τ) (hb : τ ≤ b) (hI : Icc a b ⊆ I) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hf : Measurable (fun z : ℝ × X => f z.1 z.2))
    (hweight : ∀ t, ∀ᵐ x ∂ν, (1 : ℝ) / 81 ≤ w t x)
    (hgc : AbsolutelyContinuousOnInterval (fun t => m t + C * t) a b)
    (hEm : AEStronglyMeasurable E (volume.restrict I))
    (hEn : ∀ᵐ t ∂volume, 0 ≤ E t)
    (hdata : ∀ᵐ t ∂volume, t ∈ Icc a b →
      E t ≤ 2 * deriv (fun s => m s + C * s) t ∧
      (∀ᵐ x ∂ν, 0 ≤ w t x) ∧
      Integrable (fun x => w t x * (f t x - m t)^2) ν ∧
      (∫ x, w t x * (f t x - m t)^2 ∂ν) ≤ K * E t) :
    (∀ ℓ, 0 < ℓ → ((volume.restrict (Ioc a τ)).prod ν).real
      {p : ℝ × X | m τ + ℓ < f p.1 p.2} ≤
      max (324 * K) (2 * C * (τ - a) *
        ((volume.restrict (Ioc a τ)).prod ν).real univ) / ℓ) ∧
    (∀ ℓ, 0 < ℓ → ((volume.restrict (Ioc τ b)).prod ν).real
      {p : ℝ × X | f p.1 p.2 < m τ - ℓ} ≤
      max (324 * K) (2 * C * (b - τ) *
        ((volume.restrict (Ioc τ b)).prod ν).real univ) / ℓ) := by
  have hab := ha.trans hb
  have hleft : uIcc a τ ⊆ uIcc a b := by
    rw [uIcc_of_le ha, uIcc_of_le hab]
    exact Icc_subset_Icc le_rfl hb
  have hright : uIcc τ b ⊆ uIcc a b := by
    rw [uIcc_of_le hb, uIcc_of_le hab]
    exact Icc_subset_Icc ha le_rfl
  have hleftI : uIcc a τ ⊆ I := by
    rw [uIcc_of_le ha]
    exact (Icc_subset_Icc le_rfl hb).trans hI
  have hrightI : uIcc τ b ⊆ I := by
    rw [uIcc_of_le hb]
    exact (Icc_subset_Icc ha le_rfl).trans hI
  refine ⟨?_, ?_⟩
  · exact measureReal_earlier_logarithmic_tail_le_of_ae_weight ν ha hC hK
      (fun _ _ => measurableSet_lt measurable_const hf) hweight (hgc.mono hleft)
      (hEm.mono_measure (Measure.restrict_mono hleftI le_rfl))
      (hEn.mono fun t ht _ => ht)
      (hdata.mono fun t ht hm => (ht (by simpa only [uIcc_of_le hab] using hleft hm)).1)
      (hdata.mono fun t ht hm => (ht (by simpa only [uIcc_of_le hab] using hleft hm)).2)
  · exact measureReal_later_logarithmic_tail_le_of_ae_weight ν hb hC hK
      (fun _ _ => measurableSet_lt hf measurable_const) hweight (hgc.mono hright)
      (hEm.mono_measure (Measure.restrict_mono hrightI le_rfl))
      (hEn.mono fun t ht _ => ht)
      (hdata.mono fun t ht hm => (ht (by simpa only [uIcc_of_le hab] using hright hm)).1)
      (hdata.mono fun t ht hm => (ht (by simpa only [uIcc_of_le hab] using hright hm)).2)

end HeatKernel
