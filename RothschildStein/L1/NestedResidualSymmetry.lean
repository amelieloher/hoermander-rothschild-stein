-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.NestedResidualProducts
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace RothschildStein.L1
open G3

/-- Total nested-factor weight is permutation invariant. -/
theorem nestedResidualWeight_perm {a : ℕ} (p : Fin a → ℕ+)
    {I J : List (Nested (Fin a))} (h : I.Perm J) :
    nestedResidualWeight p I = nestedResidualWeight p J := (h.map _).sum_eq

/-- Adjacent interchange proves full residual
permutation invariance within the cutoff, without any higher-weight premise. -/
theorem residual_product_eq_of_perm_lower {a r σ : ℕ} (p : Fin a → ℕ+)
    (R : MonoidAlgebra ℝ (FreeMonoid (Fin a)) →ₗ[ℝ] ℝ)
    (hshort : ∀ I : List (Nested (Fin a)), I.length < r → nestedResidualWeight p I ≤ σ →
      R (nestedResidualProduct I) = 0)
    {I J : List (Nested (Fin a))} (h : I.Perm J) :
    ∀ P : List (Nested (Fin a)), P.length + I.length ≤ r →
      nestedResidualWeight p P + nestedResidualWeight p I ≤ σ →
      R (nestedResidualProduct (P ++ I)) = R (nestedResidualProduct (P ++ J)) := by
  induction h with
  | nil => intro P _ _; rfl
  | @cons u I J h ih =>
    intro P hlen hw
    have hl' : (P ++ [u]).length + I.length ≤ r := by
      simp only [List.length_append,List.length_cons,List.length_nil] at hlen ⊢
      omega
    have hw' : nestedResidualWeight p (P ++ [u]) + nestedResidualWeight p I ≤ σ := by
      simpa only [nestedResidualWeight,List.map_append,List.sum_append,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,Nat.add_zero,Nat.add_assoc] using hw
    simpa only [List.append_assoc,List.singleton_append] using ih (P ++ [u]) hl' hw'
  | swap u v Q =>
    intro P hlen hw
    apply residual_prefix_swap_of_lower_products p R hshort P Q v u
    · simp only [List.length_cons] at hlen
      omega
    · simpa only [nestedResidualWeight,List.map_cons,List.sum_cons,Nat.add_assoc] using hw
  | trans h₁ h₂ ih₁ ih₂ =>
    intro P hlen hw
    exact (ih₁ P hlen hw).trans (ih₂ P
      (by simpa only [← h₁.length_eq] using hlen)
      (by simpa only [← nestedResidualWeight_perm p h₁] using hw))
end RothschildStein.L1
