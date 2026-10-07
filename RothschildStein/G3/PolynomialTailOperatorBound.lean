-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.ExponentialPolynomialRemainder
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped BigOperators
namespace RothschildStein.G3

/-- A polynomial supported through a weighted horizon is represented
exactly in that finite quotient. -/
theorem finitePolynomial_restrict_polynomial_exact {a H : ℕ} {p : Fin a → ℕ+}
    (P : MonoidAlgebra ℝ (FreeMonoid (Fin a)))
    (hP : ∀ I, H < wordWeight p I → polynomialSeries a P I = 0) :
    finitePolynomial (restrict (s := H) (p := p) (polynomialSeries a P)) = P := by
  apply polynomialSeries_injective a
  rw [polynomialSeries_finitePolynomial]
  funext I
  by_cases hI : wordWeight p I ≤ H
  · exact extend_restrict _ I hI
  · rw [hP I (by omega)]
    simp only [extend, dite_eq_right hI]

/-- A polynomial tail invisible through weight s has a factor
of magnitude |delta|^(s+1), using only ordinary support-length jets.
This applies in the bracket-field alphabet (BB Lemma 9.22, pp. 413–414). -/
theorem norm_polynomial_tail_operator_le {a H s N R : ℕ} {p : Fin a → ℕ+}
    (Ω : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (δ : ℝ) (P : MonoidAlgebra ℝ (FreeMonoid (Fin a)))
    (horizon : ∀ I, H < wordWeight p I → polynomialSeries a P I = 0)
    (hzero : truncateSeries (s := s) (p := p) (polynomialSeries a P) = 0)
    (hlen : ∀ I, polynomialSeries a P I ≠ 0 → I.length ≤ R)
    (f : smoothOnFunctions Ω) {x : Fin N → ℝ} (hx : x ∈ Ω)
    {B F : ℝ} (hB : 0 ≤ B)
    (hXjet : ∀ i, ∀ j ≤ R, ‖iteratedFDeriv ℝ j (X i) x‖ ≤ B)
    (hfjet : ∀ j ≤ R, ‖iteratedFDeriv ℝ j f.val x‖ ≤ F)
    (hδ : |δ| ≤ 1) :
    ‖differentialWordEvaluation Ω (fun i => δ ^ (p i : ℕ) • X i)
        (fun i => ((hX i).const_smul (δ ^ (p i : ℕ))).congr (fun x _ => by ext j; rfl))
        P f |>.val x‖ ≤
      |δ| ^ (s + 1) * ∑ J : BoundedWord a H p,
        |polynomialSeries a P J.val| * ((2 ^ R * B) ^ J.val.length * F) := by
  let A : WordCoefficients a H p := restrict (polynomialSeries a P)
  have hAlen : ∀ J, A J ≠ 0 → J.val.length ≤ R := fun J hJ => hlen J.val hJ
  have hAzero : ∀ J, wordWeight p J.val < s + 1 → A J = 0 := by
    intro J hJ
    exact polynomial_coeff_zero_of_truncate_zero P hzero J.val (by omega)
  have hb := norm_weighted_polynomial_tail_le_of_support_length (k := s + 1)
    Ω X hX δ A f hx hB hXjet hfjet hAlen hδ hAzero
  have he : finitePolynomial A = P := finitePolynomial_restrict_polynomial_exact P horizon
  rw [he] at hb
  exact hb
end RothschildStein.G3
