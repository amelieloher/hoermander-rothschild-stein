-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.ResidualBracketNormalization
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace RothschildStein.L1
open G3

/-- Full, untruncated associative product of nested commutator factors. -/
def nestedResidualProduct {a : ℕ} (I : List (Nested (Fin a))) :
    MonoidAlgebra ℝ (FreeMonoid (Fin a)) := (I.map (fun u => bracketWordPolynomial u.letters)).prod

/-- Total weighted degree of a tuple of nested commutator factors. -/
def nestedResidualWeight {a : ℕ} (p : Fin a → ℕ+) (I : List (Nested (Fin a))) : ℕ :=
  (I.map (fun u => wordWeight p u.letters)).sum

/-- Vanishing on every lower-factor residual
makes any adjacent pair interchangeable within the same total-weight budget. -/
theorem residual_prefix_swap_of_lower_products {a r σ : ℕ} (p : Fin a → ℕ+)
    (R : MonoidAlgebra ℝ (FreeMonoid (Fin a)) →ₗ[ℝ] ℝ)
    (hshort : ∀ I : List (Nested (Fin a)), I.length < r → nestedResidualWeight p I ≤ σ →
      R (nestedResidualProduct I) = 0)
    (P Q : List (Nested (Fin a))) (u v : Nested (Fin a))
    (hlen : P.length + Q.length + 2 ≤ r)
    (hw : nestedResidualWeight p P + wordWeight p u.letters + wordWeight p v.letters +
      nestedResidualWeight p Q ≤ σ) :
    R (nestedResidualProduct (P ++ u :: v :: Q)) =
      R (nestedResidualProduct (P ++ v :: u :: Q)) := by
  apply sub_eq_zero.mp
  have hd := residual_bracket_adjacent_difference R (nestedResidualProduct P) (nestedResidualProduct Q) u v
  have hz : ∀ z ∈ normalizeBracket u v,
      (z.1 : ℝ) * R (nestedResidualProduct P * bracketWordPolynomial z.2.letters *
        nestedResidualProduct Q) = 0 := by
    intro z hz
    have hdeg := (normalizeBracket_degrees p u v z hz).2
    have hzero := hshort (P ++ z.2 :: Q) (by simp only [List.length_append,List.length_cons]; omega)
      (by simp only [nestedResidualWeight,List.map_append,List.sum_append,List.map_cons,List.sum_cons];
          change nestedResidualWeight p P + (wordWeight p z.2.letters + nestedResidualWeight p Q) ≤ σ
          rw [hdeg]
          omega)
    have he : nestedResidualProduct P * bracketWordPolynomial z.2.letters * nestedResidualProduct Q =
        nestedResidualProduct (P ++ z.2 :: Q) := by
      simp [nestedResidualProduct,List.prod_append,mul_assoc]
    rw [he,hzero,mul_zero]
  have hs : ((normalizeBracket u v).map (fun z => (z.1 : ℝ) *
      R (nestedResidualProduct P * bracketWordPolynomial z.2.letters * nestedResidualProduct Q))).sum = 0 := by
    apply List.sum_eq_zero
    intro t ht
    obtain ⟨z,hz',rfl⟩ := List.mem_map.mp ht
    exact hz z hz'
  rw [hs] at hd
  simpa only [nestedResidualProduct,List.map_append,List.prod_append,List.map_cons,List.prod_cons,
    mul_assoc] using hd
end RothschildStein.L1
