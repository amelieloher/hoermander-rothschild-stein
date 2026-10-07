-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.DifferentialBracketEvaluation
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- Untruncated associative substitution, used before weighted
finite-jet truncation (BB Lemma 9.22, pp. 413–414). -/
def associativeWordSubstitution {a b : ℕ}
    (A : Fin a → MonoidAlgebra ℝ (FreeMonoid (Fin b))) :
    MonoidAlgebra ℝ (FreeMonoid (Fin a)) →ₐ[ℝ]
      MonoidAlgebra ℝ (FreeMonoid (Fin b)) :=
  MonoidAlgebra.lift ℝ _ _ (FreeMonoid.lift A)

/-- Evaluating a substituted polynomial is substitution of its
letter evaluations, with no analytic or truncation assumption. -/
theorem associativeWordSubstitution_evaluation {a b : ℕ}
    {B : Type*} [Semiring B] [Algebra ℝ B]
    (A : Fin a → MonoidAlgebra ℝ (FreeMonoid (Fin b)))
    (F : MonoidAlgebra ℝ (FreeMonoid (Fin b)) →ₐ[ℝ] B) :
    F.comp (associativeWordSubstitution A) =
      MonoidAlgebra.lift ℝ B (FreeMonoid (Fin a)) (FreeMonoid.lift (fun i => F (A i))) := by
  apply (MonoidAlgebra.lift ℝ B (FreeMonoid (Fin a))).symm.injective
  apply FreeMonoid.hom_eq
  intro i
  simp only [MonoidAlgebra.lift_symm_apply, AlgHom.comp_apply,
    associativeWordSubstitution, MonoidAlgebra.lift_single,
    FreeMonoid.lift_eval_of, one_smul]
end RothschildStein.G3
