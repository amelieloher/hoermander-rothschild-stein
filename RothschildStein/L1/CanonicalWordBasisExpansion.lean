-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.CanonicalWordPullback
public import RothschildStein.L1.CanonicalFormalWordExpansion
public import RothschildStein.L1.FreeCanonicalCharts
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric TopologicalSpace
open scoped BigOperators
namespace RothschildStein.L1
open G3

/-- Actual retained canonical words have the same constant basis expansion
as their formal free Lie words, on the complete coefficient patch. -/
theorem canonical_wordBracket_basis_expansion {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (Ω : Opens (Fin (freeDimension a s p) → ℝ))
    (X : Fin a → (Fin (freeDimension a s p) → ℝ) → (Fin (freeDimension a s p) → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    {x : Fin (freeDimension a s p) → ℝ}
    (C : CanonicalFrameChartData Ω (canonicalWordFrame D X) x)
    (η : Fin (freeDimension a s p) → ℝ) (hη : η ∈ ball x C.radius)
    (I : List (Fin a)) (hI : wordWeight p I ≤ s)
    {u : Fin (freeDimension a s p) → ℝ} (hu : u ∈ ball 0 C.radius) :
    wordBracket (fun i => C.pullbackField η (X i)) I u =
      ∑ j, D.basis.equivFun (wordLieElement I) j • C.coordinateField η j u := by
  rw [← C.pullbackField_wordBracket Ω.isOpen X hX η hη I u hu]
  have hs := wordBracket_eq_formal_basis_sum D Ω X hX I hI (C.forward_mem (q := (η,u)) ⟨hη,hu⟩)
  change fderiv ℝ (fun ξ => C.theta (η,ξ)) (canonicalFrameMap C.time C.flow (η,u))
      (wordBracket X I (canonicalFrameMap C.time C.flow (η,u))) =
    ∑ j, D.basis.equivFun (wordLieElement I) j •
      fderiv ℝ (fun ξ => C.theta (η,ξ)) (canonicalFrameMap C.time C.flow (η,u))
        (wordBracket X (modelBasisWord D j) (canonicalFrameMap C.time C.flow (η,u)))
  rw [hs, map_sum]
  simp only [map_smul]
end RothschildStein.L1
