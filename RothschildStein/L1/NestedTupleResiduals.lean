-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.NestedResidualSymmetry
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace RothschildStein.L1
open G3

/-- The lower-factor induction hypothesis makes
the actual residual invariant under every permutation of an admissible tuple. -/
theorem residual_nested_tuple_eq_of_perm_lower {a r σ : ℕ} (p : Fin a → ℕ+)
    (R : MonoidAlgebra ℝ (FreeMonoid (Fin a)) →ₗ[ℝ] ℝ)
    (hshort : ∀ I : List (Nested (Fin a)), I.length < r → nestedResidualWeight p I ≤ σ →
      R (nestedResidualProduct I) = 0)
    (q : Fin r → Nested (Fin a)) (hw : nestedResidualWeight p (List.ofFn q) ≤ σ)
    (e : Equiv.Perm (Fin r)) :
    R (nestedResidualProduct (List.ofFn (fun i => q (e i)))) =
      R (nestedResidualProduct (List.ofFn q)) := by
  have hp : (List.ofFn (fun i => q (e i))).Perm (List.ofFn q) := e.ofFn_comp_perm q
  have hw' : nestedResidualWeight p (List.ofFn (fun i => q (e i))) ≤ σ :=
    (nestedResidualWeight_perm p hp).trans_le hw
  simpa only [List.nil_append] using residual_product_eq_of_perm_lower p R hshort hp []
    (by simp) (by simpa [nestedResidualWeight] using hw')
end RothschildStein.L1
