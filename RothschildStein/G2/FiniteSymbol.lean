-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.ExponentialTests
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Algebra.BigOperators.Finsupp.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open scoped BigOperators
namespace RothschildStein.G2
variable {N : ℕ}

/-- Finite polynomial with one coefficient for each effective operator index. -/
def finiteSymbol (A : Finset (Fin N → ℕ)) (c : (Fin N → ℕ) → ℝ) :
    MvPolynomial (Fin N) ℝ :=
  ∑ a ∈ A, MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm a) (c a)

/-- Evaluation of a finite differential symbol. -/
theorem finiteSymbol_eval (A : Finset (Fin N → ℕ)) (c : (Fin N → ℕ) → ℝ)
    (z : Fin N → ℝ) :
    MvPolynomial.eval z (finiteSymbol A c) = ∑ a ∈ A, c a * ∏ j, z j ^ a j := by
  classical
  simp only [finiteSymbol, map_sum, MvPolynomial.eval_monomial]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finsupp.prod_fintype]
  · simp
  · intro i
    simp

/-- The coefficient of an effective index in a finite differential symbol. -/
theorem finiteSymbol_coeff (A : Finset (Fin N → ℕ)) (c : (Fin N → ℕ) → ℝ)
    (a : Fin N → ℕ) (ha : a ∈ A) :
    (finiteSymbol A c).coeff (Finsupp.equivFunOnFinite.symm a) = c a := by
  classical
  simp [finiteSymbol, MvPolynomial.coeff_monomial, ha]

/-- Finite monomials are
linearly independent as functions on real coordinate space (BB p. 106;
coefficient equality follows from polynomial uniqueness over the infinite field). -/
theorem finite_monomials_separate (A : Finset (Fin N → ℕ))
    (c d : (Fin N → ℕ) → ℝ)
    (h : ∀ z : Fin N → ℝ, (∑ a ∈ A, c a * ∏ j, z j ^ a j) =
      ∑ a ∈ A, d a * ∏ j, z j ^ a j) : ∀ a ∈ A, c a = d a := by
  have he : finiteSymbol A c = finiteSymbol A d := by
    apply MvPolynomial.funext
    intro z
    simpa only [finiteSymbol_eval] using h z
  intro a ha
  have hc := congrArg (fun p : MvPolynomial (Fin N) ℝ =>
    p.coeff (Finsupp.equivFunOnFinite.symm a)) he
  simpa only [finiteSymbol_coeff A _ a ha] using hc

end RothschildStein.G2
