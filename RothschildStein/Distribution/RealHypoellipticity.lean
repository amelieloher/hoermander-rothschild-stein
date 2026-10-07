-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Distribution.Hypoellipticity
public import RothschildStein.Distribution.RealDistributionComplexification

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace RothschildStein.Distribution

/-- the real-valued actual
real-test distribution has a real smooth representative, with drift
and zeroth order, using the proved complex interface and scalar adapters. -/
theorem exists_real_smooth_representative_of_distribution_equation {k N : ℕ} (hN : 0 < N)
    (Ω : Opens (Fin N → ℝ))
    (X : Fin (k + 1) → (Fin N → ℝ) → (Fin N → ℝ)) (c : (Fin N → ℝ) → ℝ)
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin N → ℝ)))
    (hspan : Hormander.Interface.LieAlgebraSpansOn (Ω : Set (Fin N → ℝ)) X)
    (hc : ContDiffOn ℝ (⊤ : ℕ∞) c (Ω : Set (Fin N → ℝ)))
    (T : Distribution Ω ℝ (⊤ : ℕ∞)) (g : (Fin N → ℝ) → ℝ)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (Ω : Set (Fin N → ℝ)))
    (heq : ∀ ψ : TestFunction Ω ℝ (⊤ : ℕ∞), T (adjointTest Ω X c hX hc ψ) =
      Distribution.ofFun Ω g volume (⊤ : ℕ∞) ψ) :
    ∃ f : (Fin N → ℝ) → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) f (Ω : Set (Fin N → ℝ)) ∧
      ∀ ψ : TestFunction Ω ℝ (⊤ : ℕ∞), T ψ = ∫ x, ψ x * f x := by
  have hgi : LocallyIntegrableOn g (Ω : Set (Fin N → ℝ)) volume :=
    hg.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet
  have hC : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => (x : ℂ)) := Complex.ofRealCLM.contDiff
  have hgc : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => (g x : ℂ)) (Ω : Set (Fin N → ℝ)) :=
    hC.comp_contDiffOn hg
  have hEqC : ∀ ψ : TestFunction Ω ℝ (⊤ : ℕ∞),
      realDistributionToComplex Ω T (adjointTest Ω X c hX hc ψ) =
      Distribution.ofFun Ω (fun x => (g x : ℂ)) volume (⊤ : ℕ∞) ψ := by
    intro ψ
    rw [← realDistributionToComplex_ofFun Ω g hgi, realDistributionToComplex_apply,
      realDistributionToComplex_apply, heq ψ]
  obtain ⟨F, hF, hrep⟩ := exists_smooth_representative_of_distribution_equation hN Ω X c hX hspan hc
    (realDistributionToComplex Ω T) (fun x => (g x : ℂ)) hgc hEqC
  exact exists_real_smooth_representative_of_complex Ω T F hF hrep

end RothschildStein.Distribution
