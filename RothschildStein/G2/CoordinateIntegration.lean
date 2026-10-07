-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.CoordinateWords

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

@[expose] public section
noncomputable section
namespace RothschildStein.G2
open Set MeasureTheory
variable {N : ℕ}

/-- Constant coordinate fields, acting through the field derivative. -/
def coordinateFields (j : Fin N) (_ : Fin N → ℝ) : Fin N → ℝ := Hormander.Interface.basisVec j

/-- Coordinate words preserve smoothness. -/
theorem coordinate_word_contDiff (l : List (Fin N)) (f : (Fin N → ℝ) → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (wordDerivative coordinateFields l f) := by
  exact contDiffOn_univ.mp (S.contDiffOn_wordDerivative ⊤ coordinateFields
    (fun _ => contDiff_const.contDiffOn) l f hf.contDiffOn)

/-- Coordinate words preserve compact support. -/
theorem coordinate_word_compact (l : List (Fin N)) (f : (Fin N → ℝ) → ℝ)
    (hf : HasCompactSupport f) : HasCompactSupport (wordDerivative coordinateFields l f) :=
  hf.of_isClosed_subset isClosed_closure (S.tsupport_wordDerivative_subset coordinateFields l f)

private theorem coordinate_word_fold (l : List (Fin N)) (f : (Fin N → ℝ) → ℝ) :
    wordDerivative coordinateFields l f = l.foldr
      (fun j g x => fderiv ℝ g x (Hormander.Interface.basisVec j)) f := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    simp only [wordDerivative, List.foldr_cons, ih]
    rfl

/-- Concatenation is composition of coordinate words. -/
theorem coordinate_word_append (l l' : List (Fin N)) (f : (Fin N → ℝ) → ℝ) :
    wordDerivative coordinateFields (l ++ l') f =
      wordDerivative coordinateFields l (wordDerivative coordinateFields l' f) := by
  simp only [coordinate_word_fold, List.foldr_append]

private theorem integrable_product (f g : (Fin N → ℝ) → ℝ)
    (hf : Continuous f) (hg : Continuous g)
    (hc : HasCompactSupport f ∨ HasCompactSupport g) : Integrable (fun x => f x * g x) := by
  have hp : HasCompactSupport (f * g) := hc.elim (fun h => h.mul_right) (fun h => h.mul_left)
  exact (hf.mul hg).integrable_of_hasCompactSupport hp

/-- Coordinate integration by parts with either factor compact
(BB transpose formula, pp. 106–108). -/
theorem integral_coordinate_word (l : List (Fin N)) (f g : (Fin N → ℝ) → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hc : HasCompactSupport f ∨ HasCompactSupport g) :
    (∫ x, wordDerivative coordinateFields l f x * g x) =
      (-1 : ℝ) ^ l.length * ∫ x, f x * wordDerivative coordinateFields l.reverse g x := by
  induction l generalizing g with
  | nil => simp [wordDerivative]
  | cons i l ih =>
    let F := wordDerivative coordinateFields l f
    have hF := coordinate_word_contDiff l f hf
    have hdF := coordinate_word_contDiff [i] F hF
    have hdg := coordinate_word_contDiff [i] g hg
    have hcF : HasCompactSupport F ∨ HasCompactSupport g :=
      hc.imp (coordinate_word_compact l f) id
    have hcdF : HasCompactSupport (wordDerivative coordinateFields [i] F) ∨ HasCompactSupport g :=
      hcF.imp (coordinate_word_compact [i] F) id
    have hcdg : HasCompactSupport F ∨ HasCompactSupport (wordDerivative coordinateFields [i] g) :=
      hcF.imp id (coordinate_word_compact [i] g)
    have h₁ := integrable_product _ _ hdF.continuous hg.continuous hcdF
    have h₂ := integrable_product _ _ hF.continuous hdg.continuous hcdg
    have h₃ := integrable_product _ _ hF.continuous hg.continuous hcF
    have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
      (f := F) (g := g) (v := Hormander.Interface.basisVec i) h₁ h₂ h₃
      (fun x _ => (hF.differentiable (by simp)).differentiableAt)
      (fun x _ => (hg.differentiable (by simp)).differentiableAt)
    have hibp' : (∫ x, wordDerivative coordinateFields [i] F x * g x) =
        -(∫ x, F x * wordDerivative coordinateFields [i] g x) := by
      change (∫ x, fderiv ℝ F x (Hormander.Interface.basisVec i) * g x) =
        -(∫ x, F x * fderiv ℝ g x (Hormander.Interface.basisVec i))
      linarith only [hibp]
    have hc' : HasCompactSupport f ∨ HasCompactSupport (wordDerivative coordinateFields [i] g) :=
      hc.imp id (coordinate_word_compact [i] g)
    have hi := ih (wordDerivative coordinateFields [i] g) hdg hc'
    rw [List.reverse_cons, coordinate_word_append]
    change (∫ x, wordDerivative coordinateFields [i] F x * g x) = _
    rw [hibp', hi]
    simp [List.length_cons, pow_succ]

/-- The reversed coordinate word is the multi-index derivative
(BB transpose formula, pp. 106–108). -/
theorem coordinate_word_reverse_partial (a : Fin N → ℕ) (f : (Fin N → ℝ) → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    wordDerivative coordinateFields (coordinateWord a).reverse f = euclideanPartial a f := by
  rw [coordinate_word_fold]
  exact coordinateWord_reverse a f hf

/-- The original coordinate word is the multi-index derivative. -/
theorem coordinate_word_partial (a : Fin N → ℕ) (f : (Fin N → ℝ) → ℝ) :
    wordDerivative coordinateFields (coordinateWord a) f = euclideanPartial a f := by
  rw [coordinate_word_fold]
  rfl

end RothschildStein.G2
