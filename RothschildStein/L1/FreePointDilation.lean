-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.WeightedRelations
public import RothschildStein.L1.FreeFramePatterns
public import Mathlib.LinearAlgebra.Isomorphisms

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators

namespace RothschildStein.L1

/-- Evaluation of the bounded-word coefficient space. -/
def wordEvaluationLinearMap {a n s : ℕ} {w : Fin a → ℕ+}
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ) :
    (BoundedWord a s w → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun c := ∑ I, c I • wordBracket X (boundedWordList I) x
  map_add' c d := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' r c := by simp [mul_smul, Finset.smul_sum]

/-- A nonzero actual frame makes word evaluation surjective. -/
theorem wordEvaluationLinearMap_surjective {a n s : ℕ} {w : Fin a → ℕ+}
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ)
    (B : Fin n → BoundedWord a s w)
    (hB : G4.frameDet (fun I => wordBracket X (boundedWordList I)) B x ≠ 0) :
    Function.Surjective (wordEvaluationLinearMap (s := s) (w := w) X x) := by
  intro v
  refine ⟨frameWordCoefficients B
    (fun i => G4.frameCoefficient (fun I => wordBracket X (boundedWordList I))
      B (fun _ => v) i x), ?_⟩
  change (∑ I, frameWordCoefficients B _ I • wordBracket X (boundedWordList I) x) = v
  rw [frameWordCoefficients_sum]
  exact (G4.frame_representation (fun I => wordBracket X (boundedWordList I))
    B (fun _ => v) hB).symm

/-- Graded scaling descends to the actual tangent space at a free
point. This is the quotient construction behind BB Proposition 10.48. -/
theorem exists_freePoint_dilation {a n s : ℕ} {w : Fin a → ℕ+}
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ)
    (hFree : FreeAt w s X x) (B : Fin n → BoundedWord a s w)
    (hB : G4.frameDet (fun I => wordBracket X (boundedWordList I)) B x ≠ 0)
    (t : ℝ) :
    ∃ D : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ), ∀ I : BoundedWord a s w,
      D (wordBracket X (boundedWordList I) x) =
        t ^ wordWeight w (boundedWordList I) • wordBracket X (boundedWordList I) x := by
  classical
  let T := wordEvaluationLinearMap (s := s) (w := w) X x
  let R : (BoundedWord a s w → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    { toFun := fun c => ∑ I, (t ^ wordWeight w (boundedWordList I) * c I) •
        wordBracket X (boundedWordList I) x
      map_add' := by intro c d; simp [mul_add, add_smul, Finset.sum_add_distrib]
      map_smul' := by intro r c; simp [mul_left_comm, mul_smul, Finset.smul_sum] }
  have hker : LinearMap.ker T ≤ LinearMap.ker R := by
    intro c hc
    exact weighted_relation_of_FreeAt X hFree c hc t
  let E := T.quotKerEquivOfSurjective (wordEvaluationLinearMap_surjective X x B hB)
  let D := ((LinearMap.ker T).liftQ R hker).comp E.symm.toLinearMap
  have hD (c : BoundedWord a s w → ℝ) : D (T c) = R c := by
    change (LinearMap.ker T).liftQ R hker (E.symm (T c)) = R c
    rw [← LinearMap.quotKerEquivOfSurjective_apply_mk T
      (wordEvaluationLinearMap_surjective X x B hB) c]
    rw [LinearEquiv.symm_apply_apply, Submodule.liftQ_apply]
  refine ⟨D, fun I => ?_⟩
  simpa [T, R, wordEvaluationLinearMap, Pi.single_apply, ite_smul] using hD (Pi.single I 1)

end RothschildStein.L1
