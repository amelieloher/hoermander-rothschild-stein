-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.WordExponentialSupport
public import RothschildStein.G3.FinitePolynomialLinear
@[expose] public section
noncomputable section
open scoped BigOperators
namespace RothschildStein.G3

/-- Linear associative input for a constant combination of fields. -/
def linearWordPolynomial {a : ℕ} (c : Fin a → ℝ) :
    MonoidAlgebra ℝ (FreeMonoid (Fin a)) :=
  ∑ i, MonoidAlgebra.single (FreeMonoid.of i) (c i)

/-- A constant field combination has ordinary factor degree one,
regardless of its letters' assigned weights (BB Lemma 9.22, pp. 413–414). -/
theorem linearWordPolynomial_homogeneous {a : ℕ} (c : Fin a → ℝ) :
    Homogeneous (fun _ : Fin a => 1) 1 (polynomialSeries a (linearWordPolynomial c)) := by
  intro I hI
  simp only [linearWordPolynomial, map_sum, polynomialSeries_single]
  change seriesCoefficientLinear I (∑ i : Fin a, c i • wordSeries [i]) = 0
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro i _
  change c i * (if I = [i] then 1 else 0) = 0
  have hne : I ≠ [i] := by intro he; subst I; simp [wordWeight] at hI
  rw [ite_eq_right hne, mul_zero]

/-- Canonical representatives retain an entire linear field input
when all letter weights fit the cutoff. -/
theorem finitePolynomial_linear_input {a s : ℕ} {q : Fin a → ℕ+}
    (hq : ∀ i, (q i : ℕ) ≤ s) (c : Fin a → ℝ) :
    let F : WordCoefficients a s q := ∑ i, c i • (truncatedBracket [i] : WordCoefficients a s q)
    finitePolynomial F = linearWordPolynomial c := by
  change finitePolynomialLinear (∑ i, c i • (truncatedBracket [i] : WordCoefficients a s q)) = _
  rw [map_sum]
  simp only [map_smul]
  unfold linearWordPolynomial
  apply Finset.sum_congr rfl
  intro i _
  change c i • finitePolynomial (restrict (wordSeries [i]) : WordCoefficients a s q) = _
  rw [finitePolynomial_restrict_word [i]
    (by simpa only [wordWeight, List.map_singleton, List.sum_singleton] using hq i)]
  rw [FreeMonoid.ofList_singleton]
  simp only [MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
end RothschildStein.G3
