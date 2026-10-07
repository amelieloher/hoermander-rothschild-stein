-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.ModelFreedom
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- The pointwise span of the model words retained by the weighted
cutoff (BB Proposition 10.54, p. 531). -/
def modelWordSpan {a s M : ℕ} {p : Fin a → ℕ+}
    (e : (Fin M → ℝ) ≃ₗ[ℝ] formalSpan a s p) (u : Fin M → ℝ) :
    Submodule ℝ (Fin M → ℝ) :=
  Submodule.span ℝ (Set.range fun I : BoundedWord a s p =>
    wordBracket (modelGenerators e) (boundedWordList I) u)

/-- The retained model words span the full tangent coordinate space
at every point (BB Proposition 10.54, p. 531). -/
theorem modelWordSpan_eq_top {a s M : ℕ} {p : Fin a → ℕ+}
    (e : (Fin M → ℝ) ≃ₗ[ℝ] formalSpan a s p) (u : Fin M → ℝ) :
    modelWordSpan e u = ⊤ := by
  let T := (modelFieldAtEquiv e u).toLinearMap.comp (coordinateRetraction e)
  have hw : ∀ I : List (Fin a), T (truncatedBracket I) = wordBracket (modelGenerators e) I u := by
    intro I
    change modelField e (coordinateRetraction e (truncatedBracket I)) u = _
    have hr : coordinateRetraction e (truncatedBracket I) = e.symm (wordLieElement I) :=
      coordinateRetraction_apply e (wordLieElement I)
    rw [hr, wordBracket_modelGenerators]
    rfl
  have hmem : ∀ f : WordCoefficients a s p, f ∈ formalSpan a s p → T f ∈ modelWordSpan e u := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨I, _, hI, rfl⟩ := hf
      rw [hw]
      exact Submodule.subset_span ⟨boundedWord p I hI, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add f g _ _ hf hg => rw [map_add]; exact Submodule.add_mem _ hf hg
    | smul r f _ hf => rw [map_smul]; exact Submodule.smul_mem _ r hf
  apply top_unique
  intro v _
  obtain ⟨f, hf⟩ := (coefficientFieldEquiv e u).surjective v
  have he : T f.val = coefficientFieldEquiv e u f := by
    change modelFieldAtEquiv e u (coordinateRetraction e f.val) = _
    rw [coordinateRetraction_apply]
    rfl
  rw [← hf, ← he]
  exact hmem f.val f.property
end RothschildStein.G3
