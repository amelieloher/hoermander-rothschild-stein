-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.CoordinateProduct
public import RothschildStein.Definitions.polynomialProduct
@[expose] public section
noncomputable section
open scoped BigOperators
namespace RothschildStein.G3

/-- Coordinate inclusion into the finite associative carrier
(BB Remark 10.51, p. 528). -/
def coordinateInclusion {a s M : ℕ} {p : Fin a → ℕ+}
    (e : (Fin M → ℝ) ≃ₗ[ℝ] formalSpan a s p) :
    (Fin M → ℝ) →ₗ[ℝ] WordCoefficients a s p :=
  (formalSpan a s p).subtype.comp e.toLinearMap

/-- A linear coordinate retraction from the surrounding associative
carrier (BB Remark 10.51, p. 528). -/
def coordinateRetraction {a s M : ℕ} {p : Fin a → ℕ+}
    (e : (Fin M → ℝ) ≃ₗ[ℝ] formalSpan a s p) :
    WordCoefficients a s p →ₗ[ℝ] (Fin M → ℝ) :=
  e.symm.toLinearMap.comp (formalSpan a s p).subtype.leftInverse

/-- Coordinate retraction is inverse on the Lie carrier (BB p. 528). -/
theorem coordinateRetraction_apply {a s M : ℕ} {p : Fin a → ℕ+}
    (e : (Fin M → ℝ) ≃ₗ[ℝ] formalSpan a s p) (f : formalSpan a s p) :
    coordinateRetraction e f.val = e.symm f := by
  change e.symm ((formalSpan a s p).subtype.leftInverse ((formalSpan a s p).subtype f)) = _
  rw [LinearMap.leftInverse_apply_of_inj (formalSpan a s p).ker_subtype]

/-- Polynomial expression for a linear coordinate inclusion
(BB p. 528). -/
def coordinateInputPolynomial {a s M : ℕ} {p : Fin a → ℕ+}
    (e : (Fin M → ℝ) ≃ₗ[ℝ] formalSpan a s p) (side : Fin M → Fin M ⊕ Fin M) :
    PolynomialCoefficients (Fin M ⊕ Fin M) a s p := fun J =>
  ∑ i, MvPolynomial.C (coordinateInclusion e (fun k => if i = k then 1 else 0) J) *
    MvPolynomial.X (side i)

/-- Input polynomials evaluate to the coordinate inclusion
(BB p. 528). -/
theorem eval_coordinateInputPolynomial {a s M : ℕ} {p : Fin a → ℕ+}
    (e : (Fin M → ℝ) ≃ₗ[ℝ] formalSpan a s p)
    (side : Fin M → Fin M ⊕ Fin M) (x : Fin M ⊕ Fin M → ℝ) :
    evalPolynomialCoefficients x (coordinateInputPolynomial e side) =
      coordinateInclusion e (fun i => x (side i)) := by
  have he := LinearMap.pi_apply_eq_sum_univ (coordinateInclusion e) (fun i => x (side i))
  funext J
  change MvPolynomial.eval x (∑ i, _) = _
  rw [he]
  simp only [map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]

/-- Polynomial expression for a linear output coordinate map
(BB p. 528). -/
def coordinateOutputPolynomial {a s M : ℕ} {p : Fin a → ℕ+}
    (e : (Fin M → ℝ) ≃ₗ[ℝ] formalSpan a s p)
    (F : PolynomialCoefficients (Fin M ⊕ Fin M) a s p) :
    Fin M → MvPolynomial (Fin M ⊕ Fin M) ℝ := fun j =>
  ∑ J, MvPolynomial.C (coordinateRetraction e (fun K => if J = K then 1 else 0) j) * F J

/-- Output polynomials evaluate to the coordinate retraction
(BB p. 528). -/
theorem eval_coordinateOutputPolynomial {a s M : ℕ} {p : Fin a → ℕ+}
    (e : (Fin M → ℝ) ≃ₗ[ℝ] formalSpan a s p)
    (F : PolynomialCoefficients (Fin M ⊕ Fin M) a s p) (x : Fin M ⊕ Fin M → ℝ) :
    (fun j => MvPolynomial.eval x (coordinateOutputPolynomial e F j)) =
      coordinateRetraction e (evalPolynomialCoefficients x F) := by
  have he := LinearMap.pi_apply_eq_sum_univ (coordinateRetraction e) (evalPolynomialCoefficients x F)
  funext j
  rw [he]
  simp only [coordinateOutputPolynomial, map_sum, map_mul, MvPolynomial.eval_C,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, evalPolynomialCoefficients, mul_comm]

/-- Explicit multivariate polynomials for the coordinate BCH product
(BB Proposition 10.52, p. 528). -/
def coordinateProductPolynomial {a s M : ℕ} {p : Fin a → ℕ+}
    (e : (Fin M → ℝ) ≃ₗ[ℝ] formalSpan a s p) :
    Fin M → MvPolynomial (Fin M ⊕ Fin M) ℝ :=
  coordinateOutputPolynomial e (polynomialCoefficientBCH
    (coordinateInputPolynomial e Sum.inl) (coordinateInputPolynomial e Sum.inr))

/-- The coordinate group law is represented by the constructed
multivariate polynomials (BB Proposition 10.52, p. 528). -/
theorem polynomialProduct_coordinateProductPolynomial {a s M : ℕ} {p : Fin a → ℕ+}
    (e : (Fin M → ℝ) ≃ₗ[ℝ] formalSpan a s p) (u v : Fin M → ℝ) :
    polynomialProduct (coordinateProductPolynomial e) u v = coordinateProduct e u v := by
  change (fun j => MvPolynomial.eval (Sum.elim u v) (coordinateOutputPolynomial e _ j)) = _
  rw [eval_coordinateOutputPolynomial, eval_polynomialCoefficientBCH,
    eval_coordinateInputPolynomial, eval_coordinateInputPolynomial]
  exact coordinateRetraction_apply e ⟨finiteBCH (e u).val (e v).val,
    finiteLieSpan_bch_mem (e u).property (e v).property⟩
end RothschildStein.G3
