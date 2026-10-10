-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.EnergyDensity
import Mathlib.Tactic.Linter

/-! # Integration by parts against closed horizontal gradients -/

@[expose] public section

noncomputable section

open Set MeasureTheory TopologicalSpace RothschildStein

namespace HeatKernel

/-- The closed horizontal gradient satisfies integration by parts against any smooth compact
scalar test when the field's formal transpose is its negative action. -/
theorem integral_energyGradient_mul_test {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (v : energyGraph (N := N) ⊤ X) (i : Fin q) {φ : (Fin N → ℝ) → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (ht : ∀ x, fieldTranspose (X i) φ x = -fieldDerivative (X i) φ x) :
    (∫ x, (v : GradientSpace (N := N) ⊤ q).snd i x * φ x) =
      -(∫ x, (v : GradientSpace (N := N) ⊤ q).fst x * fieldDerivative (X i) φ x) := by
  let ψ : TestFunction (⊤ : Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞) :=
    ⟨φ, hφ, hc, subset_univ _⟩
  have H := (energyGraph_le_weakGradientGraph ⊤ X (fun j => (hX j).contDiffOn) v.property i).2.2 ψ
  simpa only [Opens.coe_top, Measure.restrict_univ, ψ, TestFunction.coe_mk,
    wordTranspose, ht, mul_neg, integral_neg] using H

/-- Smooth compact scalar tests have smooth compact horizontal derivatives. -/
theorem contDiff_hasCompactSupport_fieldDerivative {N : ℕ}
    {X : (Fin N → ℝ) → (Fin N → ℝ)} {φ : (Fin N → ℝ) → ℝ}
    (hX : ContDiff ℝ (⊤ : ℕ∞) X) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) :
    ContDiff ℝ (⊤ : ℕ∞) (fieldDerivative X φ) ∧ HasCompactSupport (fieldDerivative X φ) := by
  refine ⟨?_, hc.of_isClosed_subset (isClosed_tsupport _) (S.tsupport_fieldDerivative_subset X φ)⟩
  simpa only [Opens.coe_top, contDiffOn_univ] using
    S.contDiffOn_fieldDerivative ⊤ X φ hX.contDiffOn hφ.contDiffOn



end HeatKernel
