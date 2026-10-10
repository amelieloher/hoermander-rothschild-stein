-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.HarnackOuterCylinder
import Mathlib.Tactic

/-! # Local logarithmic and power estimates for the Harnack comparison

The signed logarithmic tails share one shift and separating time for each
positive perturbation. The power families use every pair of nested scales and
all exponents in the stated range. These hypotheses depend only on values
almost everywhere inside the outer cylinder.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace HeatKernel
variable {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E]

/-- The two signed logarithmic tails, earlier reverse Hölder family and later
reciprocal mean-value family needed for the buffered cylinder comparison. -/
def HasHarnackCylinderEstimates (μ : Measure (ℝ × E)) (x : E)
    (t r p₀ Aminus Aplus Cminus Cplus κminus κplus : ℝ) (u : ℝ × E → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ τ c : ℝ,
    let fminus := fun y => ENNReal.ofReal (Real.exp (-c) * (u y + ε))
    let fplus := fun y => ENNReal.ofReal (Real.exp c / (u y + ε))
    t - 113 / 64 * r ^ 2 < τ ∧ τ < t - 111 / 64 * r ^ 2 ∧
    (∀ ℓ : ℝ, 0 < ℓ →
      μ ((Ioo (t - 225 / 64 * r ^ 2) τ ×ˢ Metric.ball x (5 / 4 * r)) ∩
        {y | c + ℓ < Real.log (u y + ε)}) ≤ ENNReal.ofReal (Aminus / ℓ) *
          μ (Ioo (t - 225 / 64 * r ^ 2) τ ×ˢ Metric.ball x (5 / 4 * r))) ∧
    (∀ ℓ : ℝ, 0 < ℓ →
      μ ((Ioo τ t ×ˢ Metric.ball x (5 / 4 * r)) ∩
        {y | Real.log (u y + ε) < c - ℓ}) ≤ ENNReal.ofReal (Aplus / ℓ) *
          μ (Ioo τ t ×ˢ Metric.ball x (5 / 4 * r))) ∧
    (∀ σ' σ'' : ℝ, 31 / 32 ≤ σ' → σ' < σ'' → σ'' ≤ 1 →
      ∀ p : ℝ, 0 < p → p ≤ p₀ / 2 →
      (∫⁻ y in harnackEarlierIterationCylinder x t r σ', fminus y ^ p₀ ∂μ) ^ (1 / p₀) ≤
        (ENNReal.ofReal (Cminus * (1 / (σ'' - σ')) ^ κminus) *
          (μ (harnackEarlierIterationCylinder x t r 1))⁻¹) ^ (1 / p - 1 / p₀) *
            (∫⁻ y in harnackEarlierIterationCylinder x t r σ'', fminus y ^ p ∂μ) ^ (1 / p)) ∧
    (∀ σ' σ'' : ℝ, 9 / 10 ≤ σ' → σ' < σ'' → σ'' ≤ 1 →
      ∀ p : ℝ, 0 < p → p ≤ p₀ / 2 →
      essSup fplus (μ.restrict (harnackLaterIterationCylinder x t r σ')) ≤
        (ENNReal.ofReal (Cplus * (1 / (σ'' - σ')) ^ κplus) *
          (μ (harnackLaterIterationCylinder x t r 1))⁻¹ *
            (∫⁻ y in harnackLaterIterationCylinder x t r σ'', fplus y ^ p ∂μ)) ^ (1 / p))

/-- Replacing a function on a null set inside the outer cylinder preserves all
logarithmic and power hypotheses, including their common shift and constants. -/
theorem HasHarnackCylinderEstimates.congr_ae
    {μ : Measure (ℝ × E)} {x : E} {t r p₀ Aminus Aplus Cminus Cplus κminus κplus : ℝ}
    {u v : ℝ × E → ℝ}
    (hu : HasHarnackCylinderEstimates μ x t r p₀ Aminus Aplus Cminus Cplus κminus κplus u)
    (hr : 0 < r)
    (huv : u =ᵐ[μ.restrict (Ioo (t - 4 * r ^ 2) t ×ˢ Metric.ball x (2 * r))] v) :
    HasHarnackCylinderEstimates μ x t r p₀ Aminus Aplus Cminus Cplus κminus κplus v := by
  let D := Ioo (t - 4 * r ^ 2) t ×ˢ Metric.ball x (2 * r)
  have hm (V : Set (ℝ × E)) (hV : V ⊆ D) (F : ℝ → ℝ≥0∞) :
      (∫⁻ y in V, F (u y) ∂μ) = ∫⁻ y in V, F (v y) ∂μ :=
    lintegral_congr_ae ((ae_restrict_of_ae_restrict_of_subset hV huv).mono
      fun _ hy => congrArg F hy)
  have hs (V : Set (ℝ × E)) (hV : V ⊆ D) (F : ℝ → ℝ≥0∞) :
      essSup (fun y => F (u y)) (μ.restrict V) = essSup (fun y => F (v y)) (μ.restrict V) :=
    essSup_congr_ae ((ae_restrict_of_ae_restrict_of_subset hV huv).mono
      fun _ hy => congrArg F hy)
  have ht (V : Set (ℝ × E)) (hV : V ⊆ D) (P : ℝ → Prop) :
      μ (V ∩ {y | P (u y)}) = μ (V ∩ {y | P (v y)}) := by
    apply measure_congr
    filter_upwards [ae_imp_of_ae_restrict huv] with y hy
    by_cases hmem : y ∈ V
    · simp only [mem_inter_iff, mem_ofPred_eq, hmem, true_and, hy (hV hmem)]
    · simp only [mem_inter_iff, hmem, false_and]
  have hout := harnackIterationCylinders_subset_outer x t hr
  have hminus (σ : ℝ) (hσ : 0 ≤ σ) (hσone : σ ≤ 1) :
      harnackEarlierIterationCylinder x t r σ ⊆ D :=
    ((harnackIterationCylinders_mono x t hr.le hσ hσone).1).trans hout.1
  have hplus (σ : ℝ) (hσ : 0 ≤ σ) (hσone : σ ≤ 1) :
      harnackLaterIterationCylinder x t r σ ⊆ D :=
    ((harnackIterationCylinders_mono x t hr.le hσ hσone).2).trans hout.2
  intro ε hε
  obtain ⟨τ, c, hτlower, hτupper, htminus, htplus, hreverse, hreciprocal⟩ := hu ε hε
  obtain ⟨hregionminus, hregionplus⟩ :=
    harnackLogarithmicRegions_subset_outer x t hr hτlower hτupper
  refine ⟨τ, c, hτlower, hτupper, ?_, ?_, ?_, ?_⟩
  · intro ℓ hℓ
    rw [← ht _ hregionminus (fun s => c + ℓ < Real.log (s + ε))]
    exact htminus ℓ hℓ
  · intro ℓ hℓ
    rw [← ht _ hregionplus (fun s => Real.log (s + ε) < c - ℓ)]
    exact htplus ℓ hℓ
  · intro σ' σ'' hθ hgap hσone p hp hptop
    have hσ' := hminus σ' (by linarith) (hgap.le.trans hσone)
    have hσ'' := hminus σ'' (by linarith) hσone
    rw [← hm _ hσ' (fun s => ENNReal.ofReal (Real.exp (-c) * (s + ε)) ^ p₀),
      ← hm _ hσ'' (fun s => ENNReal.ofReal (Real.exp (-c) * (s + ε)) ^ p)]
    exact hreverse σ' σ'' hθ hgap hσone p hp hptop
  · intro σ' σ'' hθ hgap hσone p hp hptop
    have hσ' := hplus σ' (by linarith) (hgap.le.trans hσone)
    have hσ'' := hplus σ'' (by linarith) hσone
    rw [← hs _ hσ' (fun s => ENNReal.ofReal (Real.exp c / (s + ε))),
      ← hm _ hσ'' (fun s => ENNReal.ofReal (Real.exp c / (s + ε)) ^ p)]
    exact hreciprocal σ' σ'' hθ hgap hσone p hp hptop

end HeatKernel
