-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.LieWords
public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Algebra.MonoidAlgebra.Basic
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- An associative word monomial in the coefficient completion
(BB (9.73), p. 467). -/
def wordSeries {a : ℕ} (I : List (Fin a)) : CoefficientSeries a :=
  fun J => if J = I then 1 else 0

/-- Left multiplication by a letter removes that first letter from the
coefficient index (BB (9.73), p. 467). -/
theorem letterSeries_mul_cons {a : ℕ} (i j : Fin a) (f : CoefficientSeries a)
    (J : List (Fin a)) :
    (letterSeries i * f) (j :: J) = if j = i then f J else 0 := by
  change wordConvolution (fun K => if K = [i] then (1 : ℝ) else 0)
    (fun K => f K) (j :: J) = _
  rw [convolution_cons]
  have hz : (if ([] : List (Fin a)) = [i] then (1 : ℝ) else 0) = 0 := by simp
  rw [hz, zero_mul, zero_add]
  by_cases hji : j = i
  · subst j
    have he : (fun K => if i :: K = [i] then (1 : ℝ) else 0) = (@wordUnit a) := by
      funext K
      simp [wordUnit]
    rw [he, convolution_unit_left, ite_eq_left rfl]
  · have he : (fun K => if j :: K = [i] then (1 : ℝ) else 0) = (fun _ => 0) := by
      funext K
      simp [hji]
    rw [he, ite_eq_right hji]
    simp [wordConvolution]

/-- Prefixing a word is multiplication by its first letter
(BB (9.73), p. 467). -/
theorem wordSeries_cons {a : ℕ} (i : Fin a) (I : List (Fin a)) :
    wordSeries (i :: I) = letterSeries i * wordSeries I := by
  funext J
  cases J with
  | nil =>
    change (if [] = i :: I then (1 : ℝ) else 0) =
      wordConvolution (fun K => if K = [i] then (1 : ℝ) else 0) (fun K => wordSeries I K) []
    rw [convolution_nil]
    simp
  | cons j J =>
    rw [letterSeries_mul_cons]
    change (if j :: J = i :: I then (1 : ℝ) else 0) =
      (if j = i then (if J = I then 1 else 0) else 0)
    by_cases hji : j = i <;> simp [hji]

/-- Multiplication of word monomials is concatenation (BB p. 467). -/
theorem wordSeries_append {a : ℕ} (I J : List (Fin a)) :
    wordSeries (I ++ J) = wordSeries I * wordSeries J := by
  induction I with
  | nil =>
    have he : wordSeries ([] : List (Fin a)) = 1 := rfl
    rw [List.nil_append, he, one_mul]
  | cons i I ih =>
    rw [List.cons_append, wordSeries_cons, wordSeries_cons, mul_assoc, ← ih]

/-- Word monomials give a monoid map into the associative completion
(BB p. 467). -/
def wordSeriesHom (a : ℕ) : FreeMonoid (Fin a) →* CoefficientSeries a where
  toFun I := wordSeries I.toList
  map_one' := rfl
  map_mul' I J := wordSeries_append I.toList J.toList

/-- Finite associative word polynomials embed algebraically in the
coefficient completion (BB pp. 467–468). -/
def polynomialSeries (a : ℕ) :
    MonoidAlgebra ℝ (FreeMonoid (Fin a)) →ₐ[ℝ] CoefficientSeries a :=
  MonoidAlgebra.lift ℝ (CoefficientSeries a) (FreeMonoid (Fin a)) (wordSeriesHom a)

/-- The embedding carries a word basis vector to its coefficient monomial
(BB p. 467). -/
theorem polynomialSeries_single {a : ℕ} (I : FreeMonoid (Fin a)) (r : ℝ) :
    polynomialSeries a (MonoidAlgebra.single I r) = r • wordSeries I.toList :=
  MonoidAlgebra.lift_single _ I r
end RothschildStein.G3
