-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.ExponentialProductRemainder
public import RothschildStein.G3.PolynomialTailOperatorBound
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped BigOperators
namespace RothschildStein.G3

/-- The discarded finite exponential product/BCH polynomial. -/
def exponentialProductPolynomialTail {a : ℕ} (s : ℕ) (p : Fin a → ℕ+)
    (P Q : MonoidAlgebra ℝ (FreeMonoid (Fin a))) : MonoidAlgebra ℝ (FreeMonoid (Fin a)) :=
  wordPolynomialExp P s * wordPolynomialExp Q s - finitePolynomial (finiteExp (finiteBCH
    (truncateSeries (s := s) (p := p) (polynomialSeries a P))
    (truncateSeries (s := s) (p := p) (polynomialSeries a Q))))

/-- Explicit finite coefficient constant for the two-flow discarded
operator tail, with ordinary support length at most 2s. -/
def exponentialProductTailCoefficientBound {a : ℕ} (s W : ℕ) (p : Fin a → ℕ+)
    (P Q : MonoidAlgebra ℝ (FreeMonoid (Fin a))) (B F : ℝ) : ℝ :=
  ∑ J : BoundedWord a (W * (2 * s)) p,
    |polynomialSeries a (exponentialProductPolynomialTail s p P Q) J.val| *
      ((2 ^ (2 * s) * B) ^ J.val.length * F)

/-- The discarded two-flow product tail has an actual operator
bound of order |delta|^(s+1) with the ordinary jet budget 2s. -/
theorem norm_exponentialProduct_tail_operator_le {a s W N : ℕ} {p : Fin a → ℕ+}
    (Ω : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hq : ∀ i, (p i : ℕ) ≤ W) (δ : ℝ)
    (P Q : MonoidAlgebra ℝ (FreeMonoid (Fin a)))
    (hP : Homogeneous (fun _ : Fin a => 1) 1 (polynomialSeries a P))
    (hQ : Homogeneous (fun _ : Fin a => 1) 1 (polynomialSeries a Q))
    (hPpos : FiniteOrderAtLeast 1 (truncateSeries (s := s) (p := p) (polynomialSeries a P)))
    (hQpos : FiniteOrderAtLeast 1 (truncateSeries (s := s) (p := p) (polynomialSeries a Q)))
    (f : smoothOnFunctions Ω) {x : Fin N → ℝ} (hx : x ∈ Ω)
    {B F : ℝ} (hB : 0 ≤ B)
    (hXjet : ∀ i, ∀ j ≤ 2 * s, ‖iteratedFDeriv ℝ j (X i) x‖ ≤ B)
    (hfjet : ∀ j ≤ 2 * s, ‖iteratedFDeriv ℝ j f.val x‖ ≤ F) (hδ : |δ| ≤ 1) :
    ‖differentialWordEvaluation Ω (fun i => δ ^ (p i : ℕ) • X i)
        (fun i => ((hX i).const_smul (δ ^ (p i : ℕ))).congr (fun x _ => by ext j; rfl))
        (exponentialProductPolynomialTail s p P Q) f |>.val x‖ ≤
      |δ| ^ (s + 1) * exponentialProductTailCoefficientBound s W p P Q B F := by
  apply norm_polynomial_tail_operator_le (H := W * (2 * s)) Ω X hX δ _ ?_
    (exponentialProduct_remainder_truncate_zero P Q hPpos hQpos) ?_ f hx hB hXjet hfjet hδ
  · intro I hI
    apply exponentialProduct_remainder_length_bound P Q hP hQ I
    have hh := wordWeight_le_bound_mul_length p W hq I
    by_contra hn
    have hm := Nat.mul_le_mul_left W (Nat.not_lt.mp hn)
    omega
  · intro I hI
    by_contra hn
    exact hI (exponentialProduct_remainder_length_bound P Q hP hQ I (Nat.not_le.mp hn))
end RothschildStein.G3
