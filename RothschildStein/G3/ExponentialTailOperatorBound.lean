-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.PolynomialTailOperatorBound
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped BigOperators
namespace RothschildStein.G3

/-- Removing exponential terms above the weighted cutoff costs
|delta|^(s+1), while only s ordinary field jets are used. In the bracket
alphabet these jets are controlled by primitive jets through 2s-1
(BB Lemma 9.22, pp. 413–414). -/
theorem norm_exponential_tail_operator_le {a s Q N : ℕ} {p : Fin a → ℕ+}
    (Ω : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hq : ∀ i, (p i : ℕ) ≤ Q)
    (δ : ℝ) (P : MonoidAlgebra ℝ (FreeMonoid (Fin a)))
    (hP : Homogeneous (fun _ : Fin a => 1) 1 (polynomialSeries a P))
    (hpos : FiniteOrderAtLeast 1 (truncateSeries (s := s) (p := p) (polynomialSeries a P)))
    (f : smoothOnFunctions Ω) {x : Fin N → ℝ} (hx : x ∈ Ω)
    {B F : ℝ} (hB : 0 ≤ B)
    (hXjet : ∀ i, ∀ j ≤ s, ‖iteratedFDeriv ℝ j (X i) x‖ ≤ B)
    (hfjet : ∀ j ≤ s, ‖iteratedFDeriv ℝ j f.val x‖ ≤ F)
    (hδ : |δ| ≤ 1) :
    let T := wordPolynomialExp P s - finitePolynomial
      (finiteExp (truncateSeries (s := s) (p := p) (polynomialSeries a P)))
    ‖differentialWordEvaluation Ω (fun i => δ ^ (p i : ℕ) • X i)
        (fun i => ((hX i).const_smul (δ ^ (p i : ℕ))).congr (fun x _ => by ext j; rfl))
        T f |>.val x‖ ≤
      |δ| ^ (s + 1) * ∑ J : BoundedWord a (Q * s) p,
        |polynomialSeries a T J.val| * ((2 ^ s * B) ^ J.val.length * F) := by
  dsimp only
  apply norm_polynomial_tail_operator_le Ω X hX δ _ ?_
    (exponentialPolynomial_remainder_truncate_zero P hpos) ?_ f hx hB hXjet hfjet hδ
  · intro I hI
    apply exponentialPolynomial_remainder_length_bound P hP I
    have hh := wordWeight_le_bound_mul_length p Q hq I
    by_contra hn
    have hm := Nat.mul_le_mul_left Q (Nat.not_lt.mp hn)
    omega
  · intro I hI
    by_contra hn
    exact hI (exponentialPolynomial_remainder_length_bound P hP I (Nat.not_le.mp hn))
end RothschildStein.G3
