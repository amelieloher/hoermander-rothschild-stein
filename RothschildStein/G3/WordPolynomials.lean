-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.WordMonomials
public import RothschildStein.G3.CompletedExponential
@[expose] public section
noncomputable section
open scoped BigOperators
namespace RothschildStein.G3

/-- The polynomial embedding preserves every associative word coefficient
(BB pp. 467–468). -/
theorem polynomialSeries_coeff {a : ℕ} (f : MonoidAlgebra ℝ (FreeMonoid (Fin a)))
    (I : List (Fin a)) : polynomialSeries a f I = f.coeff (FreeMonoid.ofList I) := by
  classical
  induction f using MonoidAlgebra.induction_linear with
  | zero => rw [map_zero]; rfl
  | add f g hf hg =>
    rw [map_add]
    change polynomialSeries a f I + polynomialSeries a g I =
      f.coeff (FreeMonoid.ofList I) + g.coeff (FreeMonoid.ofList I)
    rw [hf, hg]
  | single w r =>
    rw [polynomialSeries_single, MonoidAlgebra.coeff_single, Finsupp.single_apply]
    change r * (if I = w.toList then 1 else 0) = if w = FreeMonoid.ofList I then r else 0
    by_cases hw : w = FreeMonoid.ofList I
    · subst w; simp
    · have hI : I ≠ w.toList := by intro he; apply hw; exact congrArg FreeMonoid.ofList he.symm
      simp [hw, hI]

/-- The finite polynomial algebra embeds injectively into its coefficient
completion (BB p. 467). -/
theorem polynomialSeries_injective (a : ℕ) : Function.Injective (polynomialSeries a) := by
  intro f g he
  apply MonoidAlgebra.ext
  ext I
  have h := congrArg (fun f : CoefficientSeries a => f I.toList) he
  simpa only [polynomialSeries_coeff, FreeMonoid.ofList_toList] using h

/-- Canonical finite word polynomial representing a bounded coefficient
vector (BB (9.75), p. 468). -/
def finitePolynomial {a s : ℕ} {p : Fin a → ℕ+} (f : WordCoefficients a s p) :
    MonoidAlgebra ℝ (FreeMonoid (Fin a)) :=
  ∑ J : BoundedWord a s p, MonoidAlgebra.single (FreeMonoid.ofList J.val) (f J)

/-- A coefficient is a linear functional on the completion (BB p. 467). -/
def seriesCoefficientLinear {a : ℕ} (I : List (Fin a)) : CoefficientSeries a →ₗ[ℝ] ℝ where
  toFun f := f I
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The polynomial representative has exactly the zero-extended bounded
word coefficients (BB pp. 467–468). -/
theorem polynomialSeries_finitePolynomial {a s : ℕ} {p : Fin a → ℕ+}
    (f : WordCoefficients a s p) :
    polynomialSeries a (finitePolynomial f) = (extend f : CoefficientSeries a) := by
  classical
  rw [finitePolynomial, map_sum]
  simp only [polynomialSeries_single]
  funext I
  change seriesCoefficientLinear I (∑ J : BoundedWord a s p,
    f J • wordSeries J.val) = extend f I
  rw [map_sum]
  simp only [map_smul]
  change (∑ J : BoundedWord a s p, f J * (if I = J.val then 1 else 0)) = extend f I
  by_cases hI : wordWeight p I ≤ s
  · rw [Finset.sum_eq_single (boundedWord p I hI)]
    · simp [extend, hI, boundedWord]
    · intro J _ hJ
      have hne : I ≠ J.val := by
        intro he
        apply hJ
        exact Subtype.ext he.symm
      simp [hne]
    · simp
  · have hz : ∀ J : BoundedWord a s p, I ≠ J.val := by
      intro J he
      apply hI
      simpa only [he, boundedWordList] using boundedWord_weight J
    simp [extend, hI, hz]

/-- Restriction of the canonical polynomial representative is the original
bounded coefficient vector (BB p. 468). -/
theorem truncateSeries_finitePolynomial {a s : ℕ} {p : Fin a → ℕ+}
    (f : FiniteWordAlgebra a s p) : truncateSeries (polynomialSeries a (finitePolynomial f)) = f := by
  have h := congrArg (truncateSeries (a := a) (s := s) (p := p))
    (polynomialSeries_finitePolynomial (f : WordCoefficients a s p))
  exact h.trans (restrict_extend f)
/-- Canonical polynomial representatives preserve addition (BB p. 468). -/
theorem finitePolynomial_add {a s : ℕ} {p : Fin a → ℕ+}
    (f g : WordCoefficients a s p) : finitePolynomial (f + g) = finitePolynomial f + finitePolynomial g := by
  apply polynomialSeries_injective a
  rw [map_add, polynomialSeries_finitePolynomial, polynomialSeries_finitePolynomial,
    polynomialSeries_finitePolynomial]
  exact extend_add f g

/-- Canonical polynomial representatives preserve scalars (BB p. 468). -/
theorem finitePolynomial_smul {a s : ℕ} {p : Fin a → ℕ+}
    (r : ℝ) (f : WordCoefficients a s p) : finitePolynomial (r • f) = r • finitePolynomial f := by
  apply polynomialSeries_injective a
  rw [map_smul, polynomialSeries_finitePolynomial, polynomialSeries_finitePolynomial]
  exact extend_smul r f

/-- The zero polynomial represents the zero bounded coefficient vector (BB p. 468). -/
theorem finitePolynomial_zero {a s : ℕ} {p : Fin a → ℕ+} :
    finitePolynomial (0 : WordCoefficients a s p) = 0 := by
  apply polynomialSeries_injective a
  rw [map_zero, polynomialSeries_finitePolynomial]
  exact extend_zero

/-- The unit polynomial represents the empty-word unit (BB p. 468). -/
theorem finitePolynomial_unit {a s : ℕ} {p : Fin a → ℕ+} :
    finitePolynomial (truncatedUnit : WordCoefficients a s p) = 1 := by
  apply polynomialSeries_injective a
  rw [map_one, polynomialSeries_finitePolynomial]
  funext I
  change extend truncatedUnit I = wordUnit I
  by_cases hI : I = []
  · subst I
    simp [extend, truncatedUnit, restrict, wordUnit, wordWeight, boundedWord, boundedWordList]
  · simp [extend, truncatedUnit, restrict, wordUnit, hI, boundedWord, boundedWordList]

end RothschildStein.G3
