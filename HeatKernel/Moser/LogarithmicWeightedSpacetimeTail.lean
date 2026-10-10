-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.LogarithmicSpacetimeMeasure
public import HeatKernel.Moser.LogarithmicSpatialTail
import Mathlib.Tactic

/-! # Spacetime logarithmic tails from weighted spatial variance

Measurability and finite spatial mass give integrability of tail sections. Weighted
quadratic oscillation and a signed mean-energy inequality then control the product
measure of the tail. The spatial and time-energy assumptions remain explicit.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Filter
namespace HeatKernel

/-- A squared-tent variance estimate and a signed corrected-mean energy bound
imply weak-L¹ decay at every positive level. Below the fixed cutoff, the total
cylinder mass supplies the bound; above it, weighted variance controls the tail. -/
theorem measureReal_spacetime_tail_le_of_weighted_variance
    {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν]
    (A : ℝ → Set (ℝ × X)) (hA : ∀ ℓ, 0 < ℓ → MeasurableSet (A ℓ))
    {w f : ℝ → X → ℝ} {m q E : ℝ → ℝ} {a b L K σ : ℝ}
    (hab : a ≤ b) (hK : 0 ≤ K) (hσ : |σ| ≤ 1)
    (hq : AbsolutelyContinuousOnInterval q a b)
    (hn : ∀ t ∈ uIcc a b, 0 ≤ q t)
    (hE : IntervalIntegrable E volume a b)
    (he : ∀ᵐ t ∂volume, t ∈ uIcc a b → E t ≤ 2 * σ * deriv q t)
    (hvariance : ∀ᵐ t ∂volume, t ∈ uIcc a b →
      (∀ᵐ x ∂ν, 0 ≤ w t x) ∧
      Integrable (fun x => w t x * (f t x - m t)^2) ν ∧
      (∫ x, w t x * (f t x - m t)^2 ∂ν) ≤ K * E t)
    (htail : ∀ ℓ, 0 < ℓ → L ≤ ℓ → ∀ᵐ t ∂volume, t ∈ uIcc a b → ∀ᵐ x ∂ν, (t, x) ∈ A ℓ →
      (1 : ℝ) / 81 ≤ w t x ∧ ℓ / 2 + q t ≤ |f t x - m t|) :
    ∀ ℓ, 0 < ℓ → ((volume.restrict (Ioc a b)).prod ν).real (A ℓ) ≤
      max (324 * K) (L * ((volume.restrict (Ioc a b)).prod ν).real univ) / ℓ := by
  apply logarithmic_tail_bound_of_large_levels measureReal_nonneg
  · intro ℓ _
    exact measureReal_mono (subset_univ (A ℓ))
  intro ℓ hℓ hL
  have hsection : ∀ᵐ t ∂volume, t ∈ uIcc a b →
      ν.real (Prod.mk t ⁻¹' A ℓ) ≤ (81 * K) * (E t / (ℓ / 2 + q t)^2) := by
    filter_upwards [hvariance, htail ℓ hℓ hL] with t hv ht hmem
    obtain ⟨hw, hi, hvar⟩ := hv hmem
    have hr : 0 < ℓ / 2 + q t := by linarith [hn t hmem]
    have H := measureReal_tail_le_of_tent_variance
      ((hA ℓ hℓ).preimage measurable_prodMk_left) hr hw hi (ht hmem) hvar
    calc
      ν.real (Prod.mk t ⁻¹' A ℓ) ≤ 81 * K * E t / (ℓ / 2 + q t)^2 := H
      _ = (81 * K) * (E t / (ℓ / 2 + q t)^2) := by ring
  calc
    ((volume.restrict (Ioc a b)).prod ν).real (A ℓ) ≤ 4 * (81 * K) / ℓ :=
      measureReal_spacetime_tail_le ν (hA ℓ hℓ) hab hℓ (by positivity) hσ hq hn hE
        he hsection
    _ = 324 * K / ℓ := by ring

end HeatKernel
