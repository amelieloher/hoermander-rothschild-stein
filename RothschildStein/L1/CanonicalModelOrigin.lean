-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.CanonicalWordBasisExpansion
public import RothschildStein.G3.ModelPackage
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric TopologicalSpace
open scoped BigOperators
namespace RothschildStein.L1
open G3

/-- Actual retained canonical words have exactly their formal basis coordinates
at zero, since the chosen actual frame has standard basis values there. -/
theorem canonical_wordBracket_origin {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (Ω : Opens (Fin (freeDimension a s p) → ℝ))
    (X : Fin a → (Fin (freeDimension a s p) → ℝ) → (Fin (freeDimension a s p) → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    {x : Fin (freeDimension a s p) → ℝ}
    (C : CanonicalFrameChartData Ω (canonicalWordFrame D X) x)
    (η : Fin (freeDimension a s p) → ℝ) (hη : η ∈ ball x C.radius)
    (I : List (Fin a)) (hI : wordWeight p I ≤ s) :
    wordBracket (fun i => C.pullbackField η (X i)) I 0 = D.basis.equivFun (wordLieElement I) := by
  have hY : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (canonicalWordFrame D X j) Ω := by
    intro j
    exact G1.wordBracket_contDiffOn Ω.isOpen X hX (modelBasisWord D j)
  rw [canonical_wordBracket_basis_expansion D Ω X hX C η hη I hI (mem_ball_self C.radius_pos)]
  simp only [C.basis_values Ω.isOpen hY η hη]
  ext j
  simp [Pi.single_apply]

/-- Remainder values vanish at zero for retained words. The weight
cutoff is essential; no corresponding high-weight assertion is made. -/
theorem canonical_wordBracket_remainder_zero {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (Ω : Opens (Fin (freeDimension a s p) → ℝ))
    (X : Fin a → (Fin (freeDimension a s p) → ℝ) → (Fin (freeDimension a s p) → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    {x : Fin (freeDimension a s p) → ℝ}
    (C : CanonicalFrameChartData Ω (canonicalWordFrame D X) x)
    (η : Fin (freeDimension a s p) → ℝ) (hη : η ∈ ball x C.radius)
    (I : List (Fin a)) (hI : wordWeight p I ≤ s) :
    wordBracket (fun i => C.pullbackField η (X i)) I 0 - wordBracket D.fields I 0 = 0 := by
  rw [canonical_wordBracket_origin D Ω X hX C η hη I hI]
  have hm : wordBracket D.fields I 0 = D.basis.equivFun (wordLieElement I) := by
    rw [FreeModelData.fields, wordBracket_modelGenerators, modelField_zero, wordCoordinates]
    rfl
  rw [hm, sub_self]
end RothschildStein.L1
