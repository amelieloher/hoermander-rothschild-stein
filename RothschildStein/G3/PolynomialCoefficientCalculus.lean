-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.ModelProduct
public import Mathlib.Algebra.MvPolynomial.Eval
@[expose] public section
noncomputable section
open scoped BigOperators
namespace RothschildStein.G3

/-- Polynomial-valued associative coefficients (BB p. 528). -/
abbrev PolynomialCoefficients (σ : Type*) (a s : ℕ) (p : Fin a → ℕ+) :=
  BoundedWord a s p → MvPolynomial σ ℝ

/-- Evaluation of polynomial-valued coefficients (BB p. 528). -/
def evalPolynomialCoefficients {σ : Type*} {a s : ℕ} {p : Fin a → ℕ+}
    (x : σ → ℝ) (F : PolynomialCoefficients σ a s p) : FiniteWordAlgebra a s p :=
  fun J => MvPolynomial.eval x (F J)

/-- Zero extension for polynomial-valued coefficients (BB p. 528). -/
def extendPolynomialCoefficients {σ : Type*} {a s : ℕ} {p : Fin a → ℕ+}
    (F : PolynomialCoefficients σ a s p) (I : List (Fin a)) : MvPolynomial σ ℝ :=
  if h : wordWeight p I ≤ s then F (boundedWord p I h) else 0

/-- Evaluation commutes with zero extension (BB p. 528). -/
theorem eval_extendPolynomialCoefficients {σ : Type*} {a s : ℕ} {p : Fin a → ℕ+}
    (x : σ → ℝ) (F : PolynomialCoefficients σ a s p) (I : List (Fin a)) :
    MvPolynomial.eval x (extendPolynomialCoefficients F I) =
      extend (evalPolynomialCoefficients x F) I := by
  classical
  by_cases h : wordWeight p I ≤ s
  · simp [extendPolynomialCoefficients, extend, h, evalPolynomialCoefficients]
  · simp [extendPolynomialCoefficients, extend, h]

/-- Symbolic truncated associative multiplication (BB p. 528). -/
def polynomialCoefficientProduct {σ : Type*} {a s : ℕ} {p : Fin a → ℕ+}
    (F G : PolynomialCoefficients σ a s p) : PolynomialCoefficients σ a s p :=
  fun J => ∑ r ∈ Finset.range (J.val.length + 1),
    extendPolynomialCoefficients F (J.val.take r) * extendPolynomialCoefficients G (J.val.drop r)

/-- Symbolic multiplication evaluates to the concrete associative
multiplication (BB p. 528). -/
theorem eval_polynomialCoefficientProduct {σ : Type*} {a s : ℕ} {p : Fin a → ℕ+}
    (x : σ → ℝ) (F G : PolynomialCoefficients σ a s p) :
    evalPolynomialCoefficients x (polynomialCoefficientProduct F G) =
      evalPolynomialCoefficients x F * evalPolynomialCoefficients x G := by
  funext J
  change MvPolynomial.eval x (∑ r ∈ Finset.range (J.val.length + 1), _) =
    wordConvolution (extend (evalPolynomialCoefficients x F))
      (extend (evalPolynomialCoefficients x G)) J.val
  simp only [wordConvolution, map_sum, map_mul, eval_extendPolynomialCoefficients]

/-- Symbolic unit in the associative coefficient algebra (BB p. 528). -/
def polynomialCoefficientUnit {σ : Type*} {a s : ℕ} {p : Fin a → ℕ+} :
    PolynomialCoefficients σ a s p := fun J => MvPolynomial.C (truncatedUnit J)

/-- Symbolic powers of polynomial coefficient vectors (BB p. 528). -/
def polynomialCoefficientPow {σ : Type*} {a s : ℕ} {p : Fin a → ℕ+}
    (F : PolynomialCoefficients σ a s p) : ℕ → PolynomialCoefficients σ a s p
  | 0 => polynomialCoefficientUnit
  | n + 1 => polynomialCoefficientProduct (polynomialCoefficientPow F n) F

/-- Symbolic powers evaluate to powers in the coefficient algebra
(BB p. 528). -/
theorem eval_polynomialCoefficientPow {σ : Type*} {a s : ℕ} {p : Fin a → ℕ+}
    (x : σ → ℝ) (F : PolynomialCoefficients σ a s p) (n : ℕ) :
    evalPolynomialCoefficients x (polynomialCoefficientPow F n) =
      (evalPolynomialCoefficients x F) ^ n := by
  induction n with
  | zero => funext J; simp [polynomialCoefficientPow, polynomialCoefficientUnit, evalPolynomialCoefficients]; rfl
  | succ n ih => rw [polynomialCoefficientPow, eval_polynomialCoefficientProduct, ih, pow_succ]
end RothschildStein.G3
