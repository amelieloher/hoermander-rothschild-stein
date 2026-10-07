-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.FiniteTransposeIdentity
public import RothschildStein.S.ClassicalWords

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped BigOperators ContDiff
namespace RothschildStein.H1
variable {N : ℕ}

/-- A multi-index derivative loses its precise finite order. -/
theorem contDiffOn_euclideanPartial_finite (U : Opens (Fin N → ℝ))
    (a : Fin N → ℕ) (k : ℕ) (f : (Fin N → ℝ) → ℝ)
    (hf : ContDiffOn ℝ ((k + ∑ j, a j : ℕ) : ℕ∞ω) f (U : Set (Fin N → ℝ))) :
    ContDiffOn ℝ k (euclideanPartial a f) (U : Set (Fin N → ℝ)) := by
  have hX (j : Fin N) : ContDiffOn ℝ (⊤ : ℕ∞) (G2.coordinateFields j)
      (U : Set (Fin N → ℝ)) := contDiffOn_const
  have h := S.contDiffOn_wordDerivative_finite U G2.coordinateFields hX (G2.coordinateWord a) k f
    (by simpa only [G2.coordinateWord_length] using hf)
  simpa only [G2.coordinate_word_partial] using h

/-- Step 1: coordinate words integrate by parts with exactly
their length of local differentiability, against an interior test. -/
theorem integral_coordinateWord_mul_test (U : Opens (Fin N → ℝ))
    (l : List (Fin N)) (f : (Fin N → ℝ) → ℝ)
    (hf : ContDiffOn ℝ l.length f (U : Set (Fin N → ℝ)))
    (φ : TestFunction U ℝ (⊤ : ℕ∞)) :
    (∫ x in (U : Set (Fin N → ℝ)), wordDerivative G2.coordinateFields l f x * φ x) =
      (-1 : ℝ) ^ l.length * ∫ x in (U : Set (Fin N → ℝ)),
        f x * wordDerivative G2.coordinateFields l.reverse φ x := by
  induction l generalizing f φ with
  | nil => simp [wordDerivative]
  | cons i l ih =>
    have hX (j : Fin N) : ContDiffOn ℝ (⊤ : ℕ∞) (G2.coordinateFields j)
        (U : Set (Fin N → ℝ)) := contDiffOn_const
    let dφ := S.wordDerivativeTest U G2.coordinateFields hX [i] φ
    have hdφ : (dφ : (Fin N → ℝ) → ℝ) = wordDerivative G2.coordinateFields [i] φ := rfl
    have htail : ContDiffOn ℝ 1 (wordDerivative G2.coordinateFields l f)
        (U : Set (Fin N → ℝ)) :=
      S.contDiffOn_wordDerivative_finite U G2.coordinateFields hX l 1 f
        (by simpa [Nat.add_comm] using hf)
    have hibp := S.integral_coordinate_mul_test U _ htail φ (Hormander.Interface.basisVec i)
    have hi := ih f (hf.of_le (by simp)) dφ
    rw [hdφ] at hi
    rw [List.reverse_cons, G2.coordinate_word_append]
    change (∫ x in (U : Set (Fin N → ℝ)),
      fderiv ℝ (wordDerivative G2.coordinateFields l f) x (Hormander.Interface.basisVec i) * φ x) = _
    rw [hibp]
    change -(∫ x in (U : Set (Fin N → ℝ)),
      wordDerivative G2.coordinateFields l f x * wordDerivative G2.coordinateFields [i] φ x) = _
    rw [hi]
    simp [List.length_cons, pow_succ]

/-- The multi-index integration-by-parts identity on an open
set needs precisely the total multi-index order of local regularity
(BB Corollary 6.31, p. 280). -/
theorem integral_euclideanPartial_mul_test (U : Opens (Fin N → ℝ))
    (a : Fin N → ℕ) (f : (Fin N → ℝ) → ℝ)
    (hf : ContDiffOn ℝ (∑ j, a j : ℕ) f (U : Set (Fin N → ℝ)))
    (φ : TestFunction U ℝ (⊤ : ℕ∞)) :
    (∫ x in (U : Set (Fin N → ℝ)), euclideanPartial a f x * φ x) =
      (-1 : ℝ) ^ (∑ j, a j) * ∫ x in (U : Set (Fin N → ℝ)),
        f x * euclideanPartial a φ x := by
  have h := integral_coordinateWord_mul_test U (G2.coordinateWord a) f
    (by simpa only [G2.coordinateWord_length] using hf) φ
  simpa only [G2.coordinate_word_partial, G2.coordinate_word_reverse_partial a φ φ.contDiff,
    G2.coordinateWord_length] using h

end RothschildStein.H1
