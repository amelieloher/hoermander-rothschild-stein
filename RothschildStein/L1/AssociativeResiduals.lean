-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.DifferentialWordEvaluation
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.L1

/-- Evaluation of an actual associative differential polynomial at a smooth
function and base point, as a linear functional on the word algebra. -/
def differentialPolynomialAt {a N : ℕ} (Ω : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (u : G3.smoothOnFunctions Ω) (x : Fin N → ℝ) :
    MonoidAlgebra ℝ (FreeMonoid (Fin a)) →ₗ[ℝ] ℝ where
  toFun P := (G3.differentialWordEvaluation Ω X hX P u).val x
  map_add' P Q := by simp only [map_add,LinearMap.add_apply,Submodule.coe_add,Pi.add_apply]
  map_smul' t P := by
    simp only [map_smul,LinearMap.smul_apply,Submodule.coe_smul,Pi.smul_apply,RingHom.id_apply]

/-- Adjacent interchange is exactly the residual
of the shortened product with the associative commutator replacing the pair. -/
theorem linear_residual_adjacent_difference {A : Type*} [Ring A] [Algebra ℝ A]
    (R : A →ₗ[ℝ] ℝ) (P x y Q : A) :
    R (P*x*y*Q) - R (P*y*x*Q) = R (P*(x*y-y*x)*Q) := by
  rw [mul_sub,mul_sub_right_distrib,map_sub]
  simp only [mul_assoc]

end RothschildStein.L1
