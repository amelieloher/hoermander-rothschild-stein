-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Distribution.SmoothDistributionGluing

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace RothschildStein.Distribution

/-- a complex smooth representative of
an actual real-valued distribution yields a real smooth representative
by taking its real part. All compact real tests retain their pairing. -/
theorem exists_real_smooth_representative_of_complex {N : ℕ}
    (Ω : Opens (Fin N → ℝ)) (T : Distribution Ω ℝ (⊤ : ℕ∞))
    (F : (Fin N → ℝ) → ℂ) (hF : ContDiffOn ℝ (⊤ : ℕ∞) F (Ω : Set (Fin N → ℝ)))
    (hrep : ∀ ψ : TestFunction Ω ℝ (⊤ : ℕ∞), (T ψ : ℂ) = ∫ x, ψ x • F x) :
    ∃ f : (Fin N → ℝ) → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) f (Ω : Set (Fin N → ℝ)) ∧
      ∀ ψ : TestFunction Ω ℝ (⊤ : ℕ∞), T ψ = ∫ x, ψ x * f x := by
  have hR : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℂ => z.re) := Complex.reCLM.contDiff
  refine ⟨fun x => (F x).re, hR.comp_contDiffOn hF, fun ψ => ?_⟩
  have hFi : LocallyIntegrableOn F (Ω : Set (Fin N → ℝ)) volume :=
    hF.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet
  have he := congrArg Complex.re (hrep ψ)
  rw [Complex.ofReal_re] at he
  have hr : (∫ x, ψ x • F x).re = ∫ x, (ψ x • F x).re :=
    (integral_re (ψ.integrable_smul hFi)).symm
  rw [hr] at he
  exact he.trans (integral_congr_ae (Filter.Eventually.of_forall (fun x => by
    simp [Complex.real_smul])))

end RothschildStein.Distribution
