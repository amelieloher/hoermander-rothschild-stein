-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.WeightedSubstitutionCalculus
public import RothschildStein.G3.DifferentialPowerJets
public import RothschildStein.G3.DifferentialWordEvaluation
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped BigOperators
namespace RothschildStein.G3

/-- The untruncated finite exponential polynomial, with ordinary
operator-factor count at most n (BB (9.9), pp. 410–414). -/
def wordPolynomialExp {a : ℕ} (P : MonoidAlgebra ℝ (FreeMonoid (Fin a))) (n : ℕ) :
    MonoidAlgebra ℝ (FreeMonoid (Fin a)) :=
  ∑ k ∈ Finset.range (n + 1), ((k.factorial : ℝ)⁻¹) • P ^ k

/-- Weighted truncation of the ordinary degree-s exponential gives
the exact finite exponential in the cutoff-s quotient (BB pp. 413–414). -/
theorem truncate_wordPolynomialExp {a s : ℕ} {p : Fin a → ℕ+}
    (P : MonoidAlgebra ℝ (FreeMonoid (Fin a)))
    (hP : FiniteOrderAtLeast 1 (truncateSeries (s := s) (p := p) (polynomialSeries a P))) :
    truncateSeries (s := s) (p := p) (polynomialSeries a (wordPolynomialExp P s)) =
      finiteExp (truncateSeries (s := s) (p := p) (polynomialSeries a P)) := by
  simp only [wordPolynomialExp, finiteExp, map_sum, map_smul, map_pow]
  conv_rhs => rw [Finset.sum_range_succ]
  have hz : (truncateSeries (s := s) (p := p) (polynomialSeries a P)) ^ (s + 1) = 0 :=
    eq_zero_of_finiteOrderAtLeast_gt (finiteOrderAtLeast_pow hP (s + 1)) (by omega)
  rw [hz, smul_zero, add_zero]

/-- Differential evaluation of an exponential polynomial is exactly
the finite polynomial in the actual smooth differential operator. -/
theorem differentialWordEvaluation_wordPolynomialExp {a N : ℕ}
    (Ω : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (P : MonoidAlgebra ℝ (FreeMonoid (Fin a))) (n : ℕ)
    (g : smoothOnFunctions Ω) (x : Fin N → ℝ) :
    (differentialWordEvaluation Ω X hX (wordPolynomialExp P n) g).val x =
      ∑ k ∈ Finset.range (n + 1), (k.factorial : ℝ)⁻¹ *
        (((differentialWordEvaluation Ω X hX P) ^ k) g).val x := by
  simp only [wordPolynomialExp, map_sum, map_smul, map_pow, LinearMap.sum_apply,
    LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul_of_tower,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- If the polynomial operator is a field derivative, its exponential
polynomial is the actual field-power Taylor polynomial (BB (9.9), p. 411). -/
theorem differentialWordEvaluation_wordPolynomialExp_eq_fieldPowers {a N : ℕ}
    (Ω : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (P : MonoidAlgebra ℝ (FreeMonoid (Fin a)))
    (V : (Fin N → ℝ) → (Fin N → ℝ)) (hV : ContDiffOn ℝ (⊤ : ℕ∞) V Ω)
    (hP : differentialWordEvaluation Ω X hX P = smoothFieldOperator Ω V hV)
    (n : ℕ) (g : smoothOnFunctions Ω) {x : Fin N → ℝ} (hx : x ∈ Ω) :
    (differentialWordEvaluation Ω X hX (wordPolynomialExp P n) g).val x =
      ∑ k ∈ Finset.range (n + 1), (k.factorial : ℝ)⁻¹ * fieldPower V k g.val x := by
  rw [differentialWordEvaluation_wordPolynomialExp, hP]
  apply Finset.sum_congr rfl
  intro k _
  rw [smoothFieldOperator_pow_apply Ω V hV k g hx]
end RothschildStein.G3
