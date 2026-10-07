-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.PolynomialCoefficientCalculus
@[expose] public section
noncomputable section
open scoped BigOperators
namespace RothschildStein.G3

/-- Coefficient evaluation is real linear (BB p. 528). -/
def polynomialCoefficientsEvalLinear {σ : Type*} {a s : ℕ} {p : Fin a → ℕ+}
    (x : σ → ℝ) : PolynomialCoefficients σ a s p →ₗ[ℝ] FiniteWordAlgebra a s p where
  toFun := evalPolynomialCoefficients x
  map_add' F G := by funext J; exact map_add (MvPolynomial.eval x) (F J) (G J)
  map_smul' r F := by
    funext J
    change MvPolynomial.eval x (r • F J) = r * MvPolynomial.eval x (F J)
    simp [Algebra.smul_def]

/-- Polynomial coefficient exponential (BB p. 528). -/
def polynomialCoefficientExp {σ : Type*} {a s : ℕ} {p : Fin a → ℕ+}
    (F : PolynomialCoefficients σ a s p) : PolynomialCoefficients σ a s p :=
  ∑ n ∈ Finset.range (s + 2), ((n.factorial : ℝ)⁻¹) • polynomialCoefficientPow F n

/-- Evaluation commutes with the finite exponential polynomial
(BB p. 528). -/
theorem eval_polynomialCoefficientExp {σ : Type*} {a s : ℕ} {p : Fin a → ℕ+}
    (x : σ → ℝ) (F : PolynomialCoefficients σ a s p) :
    evalPolynomialCoefficients x (polynomialCoefficientExp F) =
      finiteExp (evalPolynomialCoefficients x F) := by
  change polynomialCoefficientsEvalLinear x _ = _
  simp only [polynomialCoefficientExp, finiteExp, map_sum, map_smul]
  congr 1
  funext n
  rw [show polynomialCoefficientsEvalLinear x (polynomialCoefficientPow F n) =
    (evalPolynomialCoefficients x F) ^ n from eval_polynomialCoefficientPow x F n]

/-- Polynomial successive logarithm correction (BB p. 528). -/
def polynomialCoefficientLog {σ : Type*} {a s : ℕ} {p : Fin a → ℕ+}
    (F : PolynomialCoefficients σ a s p) : ℕ → PolynomialCoefficients σ a s p
  | 0 => 0
  | n + 1 => polynomialCoefficientLog F n +
      (polynomialCoefficientUnit + F - polynomialCoefficientExp (polynomialCoefficientLog F n))

/-- Evaluation commutes with logarithm correction (BB p. 528). -/
theorem eval_polynomialCoefficientLog {σ : Type*} {a s : ℕ} {p : Fin a → ℕ+}
    (x : σ → ℝ) (F : PolynomialCoefficients σ a s p) (n : ℕ) :
    evalPolynomialCoefficients x (polynomialCoefficientLog F n) =
      logApprox (evalPolynomialCoefficients x F) n := by
  have hu : evalPolynomialCoefficients x (polynomialCoefficientUnit (a := a) (s := s) (p := p)) = 1 := by
    funext J
    simp [evalPolynomialCoefficients, polynomialCoefficientUnit]
    rfl
  induction n with
  | zero => rfl
  | succ n ih =>
    change polynomialCoefficientsEvalLinear x (_ + (_ + _ - _)) = _
    rw [map_add, map_sub, map_add]
    change evalPolynomialCoefficients x (polynomialCoefficientLog F n) +
      (evalPolynomialCoefficients x polynomialCoefficientUnit + evalPolynomialCoefficients x F -
        evalPolynomialCoefficients x (polynomialCoefficientExp (polynomialCoefficientLog F n))) = _
    rw [ih, hu, eval_polynomialCoefficientExp, ih]
    rfl

/-- An explicit polynomial-valued representative of finite BCH
(BB Proposition 10.52, p. 528). -/
def polynomialCoefficientBCH {σ : Type*} {a s : ℕ} {p : Fin a → ℕ+}
    (F G : PolynomialCoefficients σ a s p) : PolynomialCoefficients σ a s p :=
  polynomialCoefficientLog
    (polynomialCoefficientProduct (polynomialCoefficientExp F) (polynomialCoefficientExp G) -
      polynomialCoefficientUnit) s

/-- Finite BCH is polynomial in every coefficient of its inputs
(BB Proposition 10.52, p. 528). -/
theorem eval_polynomialCoefficientBCH {σ : Type*} {a s : ℕ} {p : Fin a → ℕ+}
    (x : σ → ℝ) (F G : PolynomialCoefficients σ a s p) :
    evalPolynomialCoefficients x (polynomialCoefficientBCH F G) =
      finiteBCH (evalPolynomialCoefficients x F) (evalPolynomialCoefficients x G) := by
  rw [polynomialCoefficientBCH, eval_polynomialCoefficientLog]
  have he : evalPolynomialCoefficients x (polynomialCoefficientProduct
      (polynomialCoefficientExp F) (polynomialCoefficientExp G) - polynomialCoefficientUnit) =
      finiteExp (evalPolynomialCoefficients x F) * finiteExp (evalPolynomialCoefficients x G) - 1 := by
    change polynomialCoefficientsEvalLinear x (_ - _) = _
    rw [map_sub]
    change evalPolynomialCoefficients x _ - evalPolynomialCoefficients x _ = _
    rw [eval_polynomialCoefficientProduct, eval_polynomialCoefficientExp, eval_polynomialCoefficientExp]
    congr 1
    funext J
    simp [evalPolynomialCoefficients, polynomialCoefficientUnit]
    rfl
  rw [he]
  rfl
end RothschildStein.G3
