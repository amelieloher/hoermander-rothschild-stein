-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.Definitions.wordConvolution
public import RothschildStein.Definitions.formalBracket
@[expose] public section
noncomputable section
open scoped BigOperators
namespace RothschildStein.G3

/-- The constant coefficient of Cauchy multiplication (BB (9.73), p. 467). -/
@[simp] theorem convolution_nil {a : ℕ} (f g : List (Fin a) → ℝ) :
    wordConvolution f g [] = f [] * g [] := by
  simp [wordConvolution]

/-- Separate the empty-prefix term of a word product (BB (9.73), p. 467). -/
theorem convolution_cons {a : ℕ} (f g : List (Fin a) → ℝ) (i : Fin a)
    (J : List (Fin a)) :
    wordConvolution f g (i :: J) = f [] * g (i :: J) +
      wordConvolution (fun K => f (i :: K)) g J := by
  simp only [wordConvolution, List.length_cons]
  rw [Finset.sum_range_succ']
  simp only [List.take_succ_cons, List.drop_succ_cons, List.take_zero, List.drop_zero]
  ring

/-- Cauchy multiplication is additive in its left input (BB p. 467). -/
theorem convolution_add_left {a : ℕ} (f g h : List (Fin a) → ℝ) (J : List (Fin a)) :
    wordConvolution (f + g) h J = wordConvolution f h J + wordConvolution g h J := by
  simp [wordConvolution, add_mul, Finset.sum_add_distrib]

/-- Cauchy multiplication is additive in its right input (BB p. 467). -/
theorem convolution_add_right {a : ℕ} (f g h : List (Fin a) → ℝ) (J : List (Fin a)) :
    wordConvolution f (g + h) J = wordConvolution f g J + wordConvolution f h J := by
  simp [wordConvolution, mul_add, Finset.sum_add_distrib]

/-- Left scalar multiplication commutes with Cauchy multiplication (BB p. 467). -/
theorem convolution_smul_left {a : ℕ} (r : ℝ) (f g : List (Fin a) → ℝ)
    (J : List (Fin a)) :
    wordConvolution (r • f) g J = r * wordConvolution f g J := by
  simp [wordConvolution, mul_assoc, Finset.mul_sum]

/-- Right scalar multiplication commutes with Cauchy multiplication (BB p. 467). -/
theorem convolution_smul_right {a : ℕ} (r : ℝ) (f g : List (Fin a) → ℝ)
    (J : List (Fin a)) :
    wordConvolution f (r • g) J = r * wordConvolution f g J := by
  simp only [wordConvolution, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Associativity of the completed associative-word coefficient multiplication,
proved one word at a time; no convergence hypothesis (BB (9.73), p. 467). -/
theorem convolution_assoc {a : ℕ} (f g h : List (Fin a) → ℝ) (J : List (Fin a)) :
    wordConvolution (wordConvolution f g) h J =
      wordConvolution f (wordConvolution g h) J := by
  induction J generalizing f g h with
  | nil => simp [mul_assoc]
  | cons i J ih =>
    rw [convolution_cons, convolution_cons, convolution_cons]
    have hs : (fun K => wordConvolution f g (i :: K)) =
        f [] • (fun K => g (i :: K)) + wordConvolution (fun K => f (i :: K)) g := by
      funext K
      exact convolution_cons f g i K
    rw [hs, convolution_add_left, convolution_smul_left, ih, convolution_nil]
    ring

/-- The associative empty word is the unit, separate from the empty bracket. -/
def wordUnit {a : ℕ} : List (Fin a) → ℝ := fun J => if J = [] then 1 else 0

/-- The empty associative word is a left unit (BB p. 467). -/
theorem convolution_unit_left {a : ℕ} (f : List (Fin a) → ℝ) (J : List (Fin a)) :
    wordConvolution wordUnit f J = f J := by
  induction J with
  | nil => simp [wordUnit]
  | cons i J _ =>
    rw [convolution_cons]
    simp [wordUnit, wordConvolution]

/-- The empty associative word is a right unit (BB p. 467). -/
theorem convolution_unit_right {a : ℕ} (f : List (Fin a) → ℝ) (J : List (Fin a)) :
    wordConvolution f wordUnit J = f J := by
  induction J generalizing f with
  | nil => simp [wordUnit]
  | cons i J ih =>
    rw [convolution_cons, ih]
    simp [wordUnit]

end RothschildStein.G3
