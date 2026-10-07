-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.ExponentialTailOperatorBound
public import RothschildStein.G3.LinearFieldEvaluation
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped BigOperators
namespace RothschildStein.G3

/-- Every linear word input has positive weighted order. -/
theorem truncate_linearWordPolynomial_order {a s : ℕ} (p : Fin a → ℕ+)
    (c : Fin a → ℝ) :
    FiniteOrderAtLeast 1 (truncateSeries (s := s) (p := p)
      (polynomialSeries a (linearWordPolynomial c))) := by
  apply (finite_positive_order_iff _).mpr
  change polynomialSeries a (linearWordPolynomial c) [] = 0
  exact linearWordPolynomial_homogeneous c [] (by simp [wordWeight])

/-- The discarded weighted exponential polynomial. -/
def exponentialPolynomialTail {a : ℕ} (s : ℕ) (p : Fin a → ℕ+)
    (P : MonoidAlgebra ℝ (FreeMonoid (Fin a))) : MonoidAlgebra ℝ (FreeMonoid (Fin a)) :=
  wordPolynomialExp P s - finitePolynomial
    (finiteExp (truncateSeries (s := s) (p := p) (polynomialSeries a P)))

/-- Explicit finite coefficient constant for the discarded tail;
ordinary factor count s controls the field jet budget. -/
def exponentialTailCoefficientBound {a : ℕ} (s Q : ℕ) (p : Fin a → ℕ+)
    (P : MonoidAlgebra ℝ (FreeMonoid (Fin a))) (B F : ℝ) : ℝ :=
  ∑ J : BoundedWord a (Q * s) p,
    |polynomialSeries a (exponentialPolynomialTail s p P) J.val| *
      ((2 ^ s * B) ^ J.val.length * F)

/-- A linear field-combination input has the weighted exponential
operator-tail bound with its explicit finite coefficient constant. -/
theorem norm_linearInput_exponential_tail_le {a s Q N : ℕ} (p : Fin a → ℕ+)
    (Ω : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hq : ∀ i, (p i : ℕ) ≤ Q) (δ : ℝ) (c : Fin a → ℝ)
    (f : smoothOnFunctions Ω) {x : Fin N → ℝ} (hx : x ∈ Ω)
    {B F : ℝ} (hB : 0 ≤ B)
    (hXjet : ∀ i, ∀ j ≤ s, ‖iteratedFDeriv ℝ j (X i) x‖ ≤ B)
    (hfjet : ∀ j ≤ s, ‖iteratedFDeriv ℝ j f.val x‖ ≤ F) (hδ : |δ| ≤ 1) :
    ‖differentialWordEvaluation Ω (fun i => δ ^ (p i : ℕ) • X i)
        (fun i => ((hX i).const_smul (δ ^ (p i : ℕ))).congr (fun x _ => by ext j; rfl))
        (exponentialPolynomialTail s p (linearWordPolynomial c)) f |>.val x‖ ≤
      |δ| ^ (s + 1) * exponentialTailCoefficientBound s Q p (linearWordPolynomial c) B F :=
  norm_exponential_tail_operator_le Ω X hX hq δ _
    (linearWordPolynomial_homogeneous c) (truncate_linearWordPolynomial_order p c)
    f hx hB hXjet hfjet hδ
end RothschildStein.G3
