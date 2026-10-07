-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.Convolution
public import RothschildStein.G3.FiniteWords
@[expose] public section
noncomputable section
open scoped BigOperators
namespace RothschildStein.G3

/-- Homogeneity in the associative word coefficient carrier
(BB Proposition 10.42, p. 523). -/
def Homogeneous {a : ℕ} (p : Fin a → ℕ+) (k : ℕ) (f : List (Fin a) → ℝ) : Prop :=
  ∀ J, wordWeight p J ≠ k → f J = 0

/-- A generator has its assigned positive weight (BB Proposition 10.42, p. 523). -/
theorem homogeneous_letter {a : ℕ} (p : Fin a → ℕ+) (i : Fin a) :
    Homogeneous p (p i) (fun J => if J = [i] then 1 else 0) := by
  intro J h
  by_cases hJ : J = [i]
  · subst J
    exact False.elim (h (by simp [wordWeight]))
  · simp [hJ]

/-- Multiplication adds homogeneous weights (BB Proposition 10.42, p. 523). -/
theorem homogeneous_convolution {a : ℕ} (p : Fin a → ℕ+) {k l : ℕ}
    {f g : List (Fin a) → ℝ} (hf : Homogeneous p k f) (hg : Homogeneous p l g) :
    Homogeneous p (k + l) (wordConvolution f g) := by
  intro J hJ
  unfold wordConvolution
  apply Finset.sum_eq_zero
  intro r _
  by_cases hpre : wordWeight p (J.take r) = k
  · by_cases hsuf : wordWeight p (J.drop r) = l
    · have h := weight_append p (J.take r) (J.drop r)
      rw [List.take_append_drop, hpre, hsuf] at h
      exact False.elim (hJ h)
    · rw [hg _ hsuf, mul_zero]
  · rw [hf _ hpre, zero_mul]

/-- Each right-nested formal commutator is homogeneous of precisely its
word weight (BB (10.51), p. 524). -/
theorem formalBracket_homogeneous {a : ℕ} (p : Fin a → ℕ+) (I : List (Fin a)) :
    Homogeneous p (wordWeight p I) (formalBracket I) := by
  induction I with
  | nil => intro J _; rfl
  | cons i I ih =>
    cases I with
    | nil => simpa [formalBracket, wordWeight] using homogeneous_letter p i
    | cons j I =>
      have h₁ := homogeneous_convolution p (homogeneous_letter p i) ih
      have h₂ := homogeneous_convolution p ih (homogeneous_letter p i)
      intro J hJ
      have hweight : wordWeight p (i :: j :: I) = (p i : ℕ) + wordWeight p (j :: I) := by
        simp [wordWeight]
      rw [hweight] at hJ
      exact sub_eq_zero.mpr (by rw [h₁ J hJ, h₂ J (by simpa [Nat.add_comm] using hJ)])

/-- A formal bracket above the cutoff is zero in the fixed truncated carrier
(BB Proposition 10.44, pp. 524–525). -/
theorem truncatedBracket_eq_zero_of_weight_gt {a s : ℕ} {p : Fin a → ℕ+}
    (I : List (Fin a)) (hI : s < wordWeight p I) :
    (truncatedBracket I : WordCoefficients a s p) = 0 := by
  funext J
  apply formalBracket_homogeneous p I (boundedWordList J)
  have hJ := boundedWord_weight J
  omega

/-- Constant coefficients of nonempty formal commutators vanish
(BB (10.51), p. 524). -/
theorem formalBracket_constant_zero {a : ℕ} (I : List (Fin a)) :
    formalBracket I [] = 0 := by
  cases I with
  | nil => rfl
  | cons i I =>
    apply formalBracket_homogeneous (fun _ : Fin a => 1) (i :: I) []
    simp [wordWeight]
    omega

/-- The retained one-letter generators are linearly independent
(BB Remark 10.49, p. 526). -/
theorem generators_linearIndependent {a s : ℕ} (p : Fin a → ℕ+)
    (hp : ∀ i, (p i : ℕ) ≤ s) :
    LinearIndependent ℝ (fun i : Fin a => (truncatedBracket [i] : WordCoefficients a s p)) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c h i
  let J : BoundedWord a s p := boundedWord p [i] (by simpa [wordWeight] using hp i)
  have he := congrFun h J
  simpa [truncatedBracket, boundedWordList, J, boundedWord, formalBracket,
    Finset.sum_apply] using he

end RothschildStein.G3
