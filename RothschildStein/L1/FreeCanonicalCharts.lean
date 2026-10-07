-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.CanonicalChartConstruction
public import RothschildStein.L1.DirectEvaluationBasis
public import RothschildStein.G3.ModelBasisWords
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.L1
open G3

/-- The actual homogeneous commutator frame chosen by the free model. -/
def canonicalWordFrame {a s : ℕ} {p : Fin a → ℕ+} (D : FreeModelData a s p)
    (X : Fin a → (Fin (freeDimension a s p) → ℝ) → (Fin (freeDimension a s p) → ℝ))
    (j : Fin (freeDimension a s p)) :
    (Fin (freeDimension a s p) → ℝ) → (Fin (freeDimension a s p) → ℝ) :=
  wordBracket X (modelBasisWord D j)

/-- The chosen formal basis is an actual square tangent frame
at every free point, for arbitrary positive letter weights. -/
theorem canonicalWordFrame_linearIndependent {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (Ω : Opens (Fin (freeDimension a s p) → ℝ))
    (X : Fin a → (Fin (freeDimension a s p) → ℝ) → (Fin (freeDimension a s p) → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (x : Fin (freeDimension a s p) → ℝ) (hx : x ∈ Ω) (hfree : FreeAt p s X x) :
    LinearIndependent ℝ (fun j => canonicalWordFrame D X j x) := by
  have hi := (freeAt_iff_directPointEvaluation_injective Ω X hX hx).mp hfree
  have hlin := (directPointEvaluation_injective_iff_basis_independent Ω X hX x D.basis).mp hi
  have he : (fun j => directPointEvaluation (s := s) (p := p) Ω X hX x (D.basis j)) =
      (fun j => canonicalWordFrame D X j x) := by
    funext j
    have hw : D.basis j = wordLieElement (modelBasisWord D j) :=
      Subtype.ext (modelBasisWord_spec D j).2.2
    rw [hw,directPointEvaluation_word Ω X hX _ (modelBasisWord_spec D j).2.1 hx]
    rfl
  rwa [he] at hlin

/-- Free smooth fields construct actual homogeneous-basis
canonical charts; this instantiates the chart construction for the lift,
including weight-two drift alphabets. -/
theorem nonempty_freeCanonicalFrameChartData {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (Ω : Opens (Fin (freeDimension a s p) → ℝ))
    (X : Fin a → (Fin (freeDimension a s p) → ℝ) → (Fin (freeDimension a s p) → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (x : Fin (freeDimension a s p) → ℝ) (hx : x ∈ Ω) (hfree : FreeAt p s X x) :
    Nonempty (CanonicalFrameChartData Ω (canonicalWordFrame D X) x) :=
  nonempty_canonicalFrameChartData Ω Ω.isOpen (canonicalWordFrame D X)
    (fun j => by
      simpa only [canonicalWordFrame] using G1.wordBracket_contDiffOn Ω.isOpen X hX (modelBasisWord D j)) x hx
    (canonicalWordFrame_linearIndependent D Ω X hX x hx hfree)
end RothschildStein.L1
