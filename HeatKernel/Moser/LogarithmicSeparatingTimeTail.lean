-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.LogarithmicWeightedSpacetimeTail
public import HeatKernel.Moser.LogarithmicTailSeparation
public import HeatKernel.Moser.LogarithmicTimeEnergyBudget
import Mathlib.Tactic
import all Mathlib.Basic.Real.Basic

/-! # Logarithmic tails around a separating time -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
namespace HeatKernel

/-- The earlier upper tail has weak-L¹ decay when weighted variance is controlled
by the energy of a monotone linearly corrected mean. -/
theorem measureReal_earlier_logarithmic_tail_le_of_ae_weight
    {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν]
    {w f : ℝ → X → ℝ} {m E : ℝ → ℝ} {a τ C K : ℝ}
    (hab : a ≤ τ) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hA : ∀ ℓ, 0 < ℓ → MeasurableSet {p : ℝ × X | m τ + ℓ < f p.1 p.2})
    (hweight : ∀ t, ∀ᵐ x ∂ν, (1 : ℝ) / 81 ≤ w t x)
    (hgc : AbsolutelyContinuousOnInterval (fun t => m t + C * t) a τ)
    (hEm : AEStronglyMeasurable E (volume.restrict (uIcc a τ)))
    (hEn : ∀ᵐ t ∂volume, t ∈ uIcc a τ → 0 ≤ E t)
    (he : ∀ᵐ t ∂volume, t ∈ uIcc a τ →
      E t ≤ 2 * deriv (fun s => m s + C * s) t)
    (hvariance : ∀ᵐ t ∂volume, t ∈ uIcc a τ →
      (∀ᵐ x ∂ν, 0 ≤ w t x) ∧
      Integrable (fun x => w t x * (f t x - m t)^2) ν ∧
      (∫ x, w t x * (f t x - m t)^2 ∂ν) ≤ K * E t) :
    ∀ ℓ, 0 < ℓ → ((volume.restrict (Ioc a τ)).prod ν).real
      {p : ℝ × X | m τ + ℓ < f p.1 p.2} ≤
      max (324 * K) (2 * C * (τ - a) *
        ((volume.restrict (Ioc a τ)).prod ν).real univ) / ℓ := by
  obtain ⟨hE, hgm, _⟩ := logarithmic_time_energy_budget hab hgc hEm hEn he
  let g := fun t => m t + C * t
  let q := fun t => g τ - g t
  have hcst : AbsolutelyContinuousOnInterval (fun _ : ℝ => g τ) a τ :=
    (show ContDiff ℝ 1 (fun _ : ℝ => g τ) from contDiff_const).contDiffOn.absolutelyContinuousOnInterval
  have hq : AbsolutelyContinuousOnInterval q a τ := hcst.sub hgc
  have hn : ∀ t ∈ uIcc a τ, 0 ≤ q t := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact sub_nonneg.mpr (hgm ht ⟨hab, le_rfl⟩ ht.2)
  have heq : ∀ᵐ t ∂volume, t ∈ uIcc a τ → E t ≤ 2 * (-1 : ℝ) * deriv q t := by
    filter_upwards [he] with t ht hmem
    dsimp only [q]
    rw [deriv_const_sub]
    have H := ht hmem
    change E t ≤ 2 * deriv g t at H
    nlinarith
  apply measureReal_spacetime_tail_le_of_weighted_variance ν
    (fun ℓ => {p : ℝ × X | m τ + ℓ < f p.1 p.2}) hA hab hK
    (by norm_num : |(-1 : ℝ)| ≤ 1) hq hn hE heq hvariance
  intro ℓ _ hL
  apply Filter.Eventually.of_forall
  intro t ht
  filter_upwards [hweight t] with x hwx hx
  rw [uIcc_of_le hab] at ht
  have hshift : C * (τ - t) ≤ ℓ / 2 := by
    nlinarith [mul_nonneg hC (sub_nonneg.mpr ht.1)]
  have htail := earlier_logarithmic_tail_subset (f t) m hshift hx
  exact ⟨hwx, htail.le.trans (le_abs_self _)⟩

/-- The later lower tail obeys the same bound, with the increasing deviation from
the corrected mean at the separating time. -/
theorem measureReal_later_logarithmic_tail_le_of_ae_weight
    {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν]
    {w f : ℝ → X → ℝ} {m E : ℝ → ℝ} {τ b C K : ℝ}
    (hab : τ ≤ b) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hA : ∀ ℓ, 0 < ℓ → MeasurableSet {p : ℝ × X | f p.1 p.2 < m τ - ℓ})
    (hweight : ∀ t, ∀ᵐ x ∂ν, (1 : ℝ) / 81 ≤ w t x)
    (hgc : AbsolutelyContinuousOnInterval (fun t => m t + C * t) τ b)
    (hEm : AEStronglyMeasurable E (volume.restrict (uIcc τ b)))
    (hEn : ∀ᵐ t ∂volume, t ∈ uIcc τ b → 0 ≤ E t)
    (he : ∀ᵐ t ∂volume, t ∈ uIcc τ b →
      E t ≤ 2 * deriv (fun s => m s + C * s) t)
    (hvariance : ∀ᵐ t ∂volume, t ∈ uIcc τ b →
      (∀ᵐ x ∂ν, 0 ≤ w t x) ∧
      Integrable (fun x => w t x * (f t x - m t)^2) ν ∧
      (∫ x, w t x * (f t x - m t)^2 ∂ν) ≤ K * E t) :
    ∀ ℓ, 0 < ℓ → ((volume.restrict (Ioc τ b)).prod ν).real
      {p : ℝ × X | f p.1 p.2 < m τ - ℓ} ≤
      max (324 * K) (2 * C * (b - τ) *
        ((volume.restrict (Ioc τ b)).prod ν).real univ) / ℓ := by
  obtain ⟨hE, hgm, _⟩ := logarithmic_time_energy_budget hab hgc hEm hEn he
  let g := fun t => m t + C * t
  let q := fun t => g t - g τ
  have hcst : AbsolutelyContinuousOnInterval (fun _ : ℝ => g τ) τ b :=
    (show ContDiff ℝ 1 (fun _ : ℝ => g τ) from contDiff_const).contDiffOn.absolutelyContinuousOnInterval
  have hq : AbsolutelyContinuousOnInterval q τ b := hgc.sub hcst
  have hn : ∀ t ∈ uIcc τ b, 0 ≤ q t := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact sub_nonneg.mpr (hgm ⟨le_rfl, hab⟩ ht ht.1)
  have heq : ∀ᵐ t ∂volume, t ∈ uIcc τ b → E t ≤ 2 * (1 : ℝ) * deriv q t := by
    filter_upwards [he] with t ht hmem
    dsimp only [q]
    rw [deriv_sub_const]
    simpa only [g, mul_one] using ht hmem
  apply measureReal_spacetime_tail_le_of_weighted_variance ν
    (fun ℓ => {p : ℝ × X | f p.1 p.2 < m τ - ℓ}) hA hab hK
    (by norm_num : |(1 : ℝ)| ≤ 1) hq hn hE heq hvariance
  intro ℓ _ hL
  apply Filter.Eventually.of_forall
  intro t ht
  filter_upwards [hweight t] with x hwx hx
  rw [uIcc_of_le hab] at ht
  have hshift : C * (t - τ) ≤ ℓ / 2 := by
    nlinarith [mul_nonneg hC (sub_nonneg.mpr ht.2)]
  have htail := later_logarithmic_tail_subset (f t) m hshift hx
  exact ⟨hwx, htail.le.trans (by simpa only [neg_sub] using neg_le_abs (f t x - m t))⟩

end HeatKernel
