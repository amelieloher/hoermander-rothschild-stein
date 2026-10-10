-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Bridge.LocalizedCombinedTests
import Mathlib.Tactic.Linter

/-! # Separated temporal tests for zero-boundary horizontal forms -/

@[expose] public section
open Set MeasureTheory TopologicalSpace RothschildStein
namespace HeatKernel

/-- Localized L² representatives of a literal value/flux smooth identity give
the same identity on all zero-boundary form tests. The smooth identity is explicit. -/
theorem timeIntegratedFormTest_eq_zero_of_tensor_identity
    (μ : Measure ℝ) [IsFiniteMeasure μ] {N q : ℕ}
    (V : Opens (Fin N → ℝ)) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    {K : Set (Fin N → ℝ)} (hVK : (V : Set (Fin N → ℝ)) ⊆ K)
    (u : ℝ → (Fin N → ℝ) → ℝ) (g : Fin q → ℝ → (Fin N → ℝ) → ℝ)
    (a : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ) (ψ : ℝ → ℝ)
    (T : Lp ℝ 2 (μ.prod (volume.restrict ((⊤ : Opens (Fin N → ℝ)) : Set (Fin N → ℝ)))))
    (F : Fin q → Lp ℝ 2 (μ.prod (volume.restrict ((⊤ : Opens (Fin N → ℝ)) : Set (Fin N → ℝ)))))
    (hT : (T : ℝ × (Fin N → ℝ) → ℝ) =ᵐ[μ.prod volume]
      (fun z => K.indicator (fun x => -(deriv ψ z.1) * u z.1 x) z.2))
    (hF : ∀ i, (F i : ℝ × (Fin N → ℝ) → ℝ) =ᵐ[μ.prod volume]
      (fun z => K.indicator (fun x => ψ z.1 * ∑ j, a z.1 x i j * g j z.1 x) z.2))
    (hweak : ∀ φ : (Fin N → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ (V : Set (Fin N → ℝ)) →
      (∫ z : ℝ × (Fin N → ℝ), -(u z.1 z.2 * (deriv ψ z.1 * φ z.2)) +
        ∑ i, ∑ j, a z.1 z.2 i j * g j z.1 z.2 *
          (ψ z.1 * fieldDerivative (X i) φ z.2) ∂μ.prod volume) = 0)
    (v : zeroBoundaryGraph V X) :
    timeIntegratedFormTest μ X T F ⟨v, zeroBoundaryGraph_le_energyGraph V X v.property⟩ = 0 := by
  apply timeIntegratedFormTest_eq_zero_of_localized_combined_identity μ V X hVK
    u g a (fun t => -(deriv ψ t)) ψ T F hT hF _ v
  intro φ hφ hc hs
  calc
    _ = ∫ z : ℝ × (Fin N → ℝ), -(u z.1 z.2 * (deriv ψ z.1 * φ z.2)) +
        ∑ i, ∑ j, a z.1 z.2 i j * g j z.1 z.2 *
          (ψ z.1 * fieldDerivative (X i) φ z.2) ∂μ.prod volume := by
      apply integral_congr_ae
      filter_upwards [] with z
      apply congrArg₂ (· + ·)
      · ring
      · apply Finset.sum_congr rfl
        intro i _
        simp only [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        ring
    _ = 0 := hweak φ hφ hc hs

end HeatKernel
