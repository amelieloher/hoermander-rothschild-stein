-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Bridge.LocalizedDataPairings
public import HeatKernel.Bridge.TimeIntegratedCombinedTests
import Mathlib.Tactic.Linter

/-! # Combined localized identities extended to zero-boundary form tests -/

@[expose] public section
open Set MeasureTheory TopologicalSpace RothschildStein
namespace HeatKernel

/-- Localized L² representatives of a literal value/flux smooth identity give
the same identity on all zero-boundary form tests. The smooth identity is explicit. -/
theorem timeIntegratedFormTest_eq_zero_of_localized_combined_identity
    (μ : Measure ℝ) [IsFiniteMeasure μ] {N q : ℕ}
    (V : Opens (Fin N → ℝ)) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    {K : Set (Fin N → ℝ)} (hVK : (V : Set (Fin N → ℝ)) ⊆ K)
    (u : ℝ → (Fin N → ℝ) → ℝ) (g : Fin q → ℝ → (Fin N → ℝ) → ℝ)
    (a : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ) (χ ψ : ℝ → ℝ)
    (T : Lp ℝ 2 (μ.prod (volume.restrict ((⊤ : Opens (Fin N → ℝ)) : Set (Fin N → ℝ)))))
    (F : Fin q → Lp ℝ 2 (μ.prod (volume.restrict ((⊤ : Opens (Fin N → ℝ)) : Set (Fin N → ℝ)))))
    (hT : (T : ℝ × (Fin N → ℝ) → ℝ) =ᵐ[μ.prod volume]
      (fun z => K.indicator (fun x => χ z.1 * u z.1 x) z.2))
    (hF : ∀ i, (F i : ℝ × (Fin N → ℝ) → ℝ) =ᵐ[μ.prod volume]
      (fun z => K.indicator (fun x => ψ z.1 * ∑ j, a z.1 x i j * g j z.1 x) z.2))
    (hweak : ∀ φ : (Fin N → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ (V : Set (Fin N → ℝ)) →
      (∫ z : ℝ × (Fin N → ℝ), (χ z.1 * u z.1 z.2) * φ z.2 +
        ∑ i, (ψ z.1 * ∑ j, a z.1 z.2 i j * g j z.1 z.2) *
          fieldDerivative (X i) φ z.2 ∂μ.prod volume) = 0)
    (v : zeroBoundaryGraph V X) :
    timeIntegratedFormTest μ X T F ⟨v, zeroBoundaryGraph_le_energyGraph V X v.property⟩ = 0 := by
  apply timeIntegratedFormTest_eq_zero_of_combined_identity μ V X T F _ v
  intro φ hφ hc hs
  have hφK : Function.support φ ⊆ K := (subset_tsupport φ).trans (hs.trans hVK)
  have hgradK (i : Fin q) : Function.support (fieldDerivative (X i) φ) ⊆ K :=
    (subset_tsupport _).trans ((S.tsupport_fieldDerivative_subset (X i) φ).trans (hs.trans hVK))
  have ht := ae_mul_eq_of_ae_spatial_indicator
    (f := fun z => χ z.1 * u z.1 z.2) hT hφK
  have hf (i : Fin q) := ae_mul_eq_of_ae_spatial_indicator
    (f := fun z => ψ z.1 * ∑ j, a z.1 z.2 i j * g j z.1 z.2) (hF i) (hgradK i)
  calc
    _ = ∫ z : ℝ × (Fin N → ℝ), (χ z.1 * u z.1 z.2) * φ z.2 +
        ∑ i, (ψ z.1 * ∑ j, a z.1 z.2 i j * g j z.1 z.2) *
          fieldDerivative (X i) φ z.2 ∂μ.prod volume := by
      apply integral_congr_ae
      filter_upwards [ht, ae_all_iff.mpr hf] with z hz hzi
      exact congrArg₂ (· + ·) hz (Finset.sum_congr rfl (fun i _ => hzi i))
    _ = 0 := hweak φ hφ hc hs

end HeatKernel
