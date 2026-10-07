-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.WordJetResiduals
public import RothschildStein.G3.BracketPolynomialCoefficients
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.L1
open G3

local instance residualPolynomialLieRing {a : ℕ} :
    LieRing (MonoidAlgebra ℝ (FreeMonoid (Fin a))) := LieRing.ofAssociativeRing

/-- Full associative polynomials retain the right-nested normalization. -/
theorem nested_eval_bracketWordPolynomial {a : ℕ} (u : Nested (Fin a)) :
    u.eval (fun i => MonoidAlgebra.single (FreeMonoid.of i) (1 : ℝ)) =
      bracketWordPolynomial u.letters := by
  induction u with
  | letter i => rfl
  | bracket i u ih =>
    rw [Nested.eval,ih]
    cases u <;> rfl

/-- Inserting a normalized bracket gives the
integer linear combination of the shortened residual products. -/
theorem residual_normalized_combination {a : ℕ}
    (R : MonoidAlgebra ℝ (FreeMonoid (Fin a)) →ₗ[ℝ] ℝ)
    (P Q : MonoidAlgebra ℝ (FreeMonoid (Fin a))) (A : List (ℤ × Nested (Fin a))) :
    R (P * evaluateCombination (fun i => MonoidAlgebra.single (FreeMonoid.of i) (1 : ℝ)) A * Q) =
      (A.map (fun z => (z.1 : ℝ) * R (P * bracketWordPolynomial z.2.letters * Q))).sum := by
  induction A with
  | nil => simp [evaluateCombination]
  | cons z A ih =>
    simp only [evaluateCombination,nested_eval_bracketWordPolynomial] at ih ⊢
    simp only [List.map_cons,List.sum_cons,mul_add,add_mul,map_add,
      mul_smul_comm,smul_mul_assoc,map_zsmul]
    rw [ih]
    simp only [zsmul_eq_mul]

/-- Adjacent residual interchange reduces to
products with one fewer factor and unchanged combined weight. -/
theorem residual_bracket_adjacent_difference {a : ℕ}
    (R : MonoidAlgebra ℝ (FreeMonoid (Fin a)) →ₗ[ℝ] ℝ)
    (P Q : MonoidAlgebra ℝ (FreeMonoid (Fin a))) (u v : Nested (Fin a)) :
    R (P * bracketWordPolynomial u.letters * bracketWordPolynomial v.letters * Q) -
      R (P * bracketWordPolynomial v.letters * bracketWordPolynomial u.letters * Q) =
      ((normalizeBracket u v).map (fun z => (z.1 : ℝ) *
        R (P * bracketWordPolynomial z.2.letters * Q))).sum := by
  rw [linear_residual_adjacent_difference]
  rw [← nested_eval_bracketWordPolynomial u,← nested_eval_bracketWordPolynomial v]
  change R (P * ⁅u.eval (fun i => MonoidAlgebra.single (FreeMonoid.of i) (1 : ℝ)),
    v.eval (fun i => MonoidAlgebra.single (FreeMonoid.of i) (1 : ℝ))⁆ * Q) = _
  rw [← normalizeBracket_eval]
  exact residual_normalized_combination R P Q (normalizeBracket u v)
end RothschildStein.L1
