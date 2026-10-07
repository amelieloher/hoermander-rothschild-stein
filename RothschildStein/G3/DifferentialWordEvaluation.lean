-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.SmoothOperatorBracket
public import RothschildStein.G3.WordPolynomials
public import RothschildStein.Definitions.wordDerivative
@[expose] public section
noncomputable section
open Set Filter TopologicalSpace
open scoped Topology
namespace RothschildStein.G3

/-- Evaluation of associative word polynomials in the actual smooth
field operators (BB Lemma 9.22, pp. 413–414). -/
def differentialWordEvaluation {a N : ℕ} (Ω : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) :
    MonoidAlgebra ℝ (FreeMonoid (Fin a)) →ₐ[ℝ] Module.End ℝ (smoothOnFunctions Ω) :=
  MonoidAlgebra.lift ℝ (Module.End ℝ (smoothOnFunctions Ω)) (FreeMonoid (Fin a))
    (FreeMonoid.lift (fun i => smoothFieldOperator Ω (X i) (hX i)))

/-- Associative word evaluation is exactly the fixed ordered field
word derivative on its open domain (BB Lemma 9.22, pp. 413–414). -/
theorem differentialWordEvaluation_word {a N : ℕ} (Ω : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (I : List (Fin a)) (f : smoothOnFunctions Ω) {x : Fin N → ℝ} (hx : x ∈ Ω) :
    ((FreeMonoid.lift (fun i => smoothFieldOperator Ω (X i) (hX i))
      (FreeMonoid.ofList I)) f).val x = wordDerivative X I f.val x := by
  induction I generalizing x with
  | nil => rfl
  | cons i I ih =>
    rw [FreeMonoid.ofList_cons, map_mul, FreeMonoid.lift_eval_of]
    change (smoothFieldOperator Ω (X i) (hX i)
      ((FreeMonoid.lift (fun j => smoothFieldOperator Ω (X j) (hX j)) (FreeMonoid.ofList I)) f)).val x = _
    rw [smoothFieldOperator_apply Ω _ _ _ hx]
    have he : ((FreeMonoid.lift (fun j => smoothFieldOperator Ω (X j) (hX j))
        (FreeMonoid.ofList I)) f).val =ᶠ[𝓝 x] wordDerivative X I f.val := by
      filter_upwards [Ω.isOpen.mem_nhds hx] with y hy
      exact ih hy
    change (fderiv ℝ _ x) (X i x) = (fderiv ℝ _ x) (X i x)
    rw [he.fderiv_eq]

/-- A single associative polynomial term maps to the same constant
multiple of its ordered differential word (BB Lemma 9.22, pp. 413–414). -/
theorem differentialWordEvaluation_single {a N : ℕ} (Ω : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (I : List (Fin a)) (c : ℝ) (f : smoothOnFunctions Ω)
    {x : Fin N → ℝ} (hx : x ∈ Ω) :
    (differentialWordEvaluation Ω X hX (MonoidAlgebra.single (FreeMonoid.ofList I) c) f).val x =
      c * wordDerivative X I f.val x := by
  rw [differentialWordEvaluation, MonoidAlgebra.lift_single]
  change c * _ = _
  rw [differentialWordEvaluation_word Ω X hX I f hx]
end RothschildStein.G3
