-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.SeriesAlgebra
public import RothschildStein.G3.FiniteAlgebra
public import RothschildStein.G3.Homogeneity
public import RothschildStein.G3.JacobiNormalization
public import Mathlib.Algebra.Lie.OfAssociative
@[expose] public section
noncomputable section
namespace RothschildStein.G3

instance seriesLieRing {a : ℕ} : LieRing (CoefficientSeries a) := LieRing.ofAssociativeRing
instance finiteWordLieRing {a s : ℕ} {p : Fin a → ℕ+} : LieRing (FiniteWordAlgebra a s p) :=
  LieRing.ofAssociativeRing

/-- Noncommuting generator in the coefficient completion (BB p. 467). -/
def letterSeries {a : ℕ} (i : Fin a) : CoefficientSeries a :=
  fun J => if J = [i] then 1 else 0

/-- A nested word is nonempty (BB Lemma 1.21, p. 12). -/
theorem Nested.letters_ne_nil {α : Type*} (u : Nested α) : u.letters ≠ [] := by
  cases u <;> simp [Nested.letters]

/-- Every nonempty list represents a right-nested bracket word (BB p. 12). -/
theorem exists_nested_of_list {α : Type*} (I : List α) (hI : I ≠ []) :
    ∃ u : Nested α, u.letters = I := by
  induction I with
  | nil => exact False.elim (hI rfl)
  | cons i I ih =>
    cases I with
    | nil => exact ⟨.letter i, rfl⟩
    | cons j I =>
      obtain ⟨u, hu⟩ := ih (by simp)
      exact ⟨.bracket i u, by simp [Nested.letters, hu]⟩

/-- Lie-ring evaluation agrees with the fixed formal commutator coefficients
(BB Lemma 1.21, p. 12, and (9.73), p. 467). -/
theorem nested_eval_formalBracket {a : ℕ} (u : Nested (Fin a)) :
    u.eval letterSeries = (formalBracket u.letters : CoefficientSeries a) := by
  induction u with
  | letter i => rfl
  | bracket i u ih =>
    rw [Nested.eval, ih]
    funext J
    cases u <;> rfl

/-- The finite quotient map is an algebra homomorphism (BB p. 525). -/
def truncateSeries {a s : ℕ} {p : Fin a → ℕ+} :
    CoefficientSeries a →ₐ[ℝ] FiniteWordAlgebra a s p where
  toFun := restrict
  map_one' := rfl
  map_mul' f g := (restrict_convolution f g).symm
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    rfl

/-- A fixed truncated commutator viewed in the associative quotient
(BB p. 525). -/
def finiteBracketWord {a s : ℕ} {p : Fin a → ℕ+} (I : List (Fin a)) :
    FiniteWordAlgebra a s p := truncatedBracket I

/-- Finite generators in the fixed coefficient model (BB p. 525). -/
def finiteLetter {a s : ℕ} {p : Fin a → ℕ+} (i : Fin a) : FiniteWordAlgebra a s p :=
  truncatedBracket [i]

/-- Nested Lie brackets in the quotient match fixed truncated brackets
(BB (10.51), p. 524). -/
theorem nested_eval_truncatedBracket {a s : ℕ} {p : Fin a → ℕ+}
    (u : Nested (Fin a)) :
    u.eval (finiteLetter (s := s) (p := p)) =
      (truncatedBracket u.letters : FiniteWordAlgebra a s p) := by
  have hm : ∀ u : Nested (Fin a),
      (truncateSeries (a := a) (s := s) (p := p)) (u.eval letterSeries) =
        u.eval finiteLetter := by
    intro u
    induction u with
    | letter i => rfl
    | bracket i u ih =>
      simp only [Nested.eval, Ring.lie_def, map_sub, map_mul, ih]
      rfl
  rw [← hm, nested_eval_formalBracket]
  rfl

/-- Jacobi normalization preserves both ordinary length and weighted degree
(BB Lemma 1.21, p. 12; BB (10.51), p. 524). -/
theorem normalizeBracket_degrees {a : ℕ} (p : Fin a → ℕ+)
    (u v : Nested (Fin a)) (z : ℤ × Nested (Fin a)) (hz : z ∈ normalizeBracket u v) :
    z.2.letters.length = u.letters.length + v.letters.length ∧
      wordWeight p z.2.letters = wordWeight p u.letters + wordWeight p v.letters := by
  have h := normalizeBracket_letters u v z hz
  constructor
  · simpa only [List.length_append] using h.length_eq
  · rw [← weight_append]
    exact (h.map (fun i => (p i : ℕ))).sum_eq

end RothschildStein.G3
