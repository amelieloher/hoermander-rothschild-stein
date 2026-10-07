-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.NestedTupleResiduals
public import RothschildStein.L1.FormalResidualForms
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.L1
open G3

/-- Within the cutoff, formal commutator coordinates retain their complete
associative representatives, even when their product is taken without truncation. -/
theorem formal_polynomial_product_nested {a s r : ℕ} {p : Fin a → ℕ+}
    (q : Fin r → Nested (Fin a)) (hI : ∀ i, wordWeight p (q i).letters ≤ s) :
    (List.ofFn (fun i => finitePolynomialLinear
      (wordLieElement (q i).letters : formalSpan a s p).val)).prod =
      nestedResidualProduct (List.ofFn q) := by
  simp only [nestedResidualProduct,List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext i
  change finitePolynomial (truncatedBracket (q i).letters : WordCoefficients a s p) =
    bracketWordPolynomial (q i).letters
  exact finitePolynomial_truncatedBracket _ (hI i)

/-- The abstract multilinear residual is the actual nested-product residual. -/
theorem formalResidualForm_nested {a s N r : ℕ} {p : Fin a → ℕ+}
    (Ω : Opens (Fin N → ℝ)) (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) (u : smoothOnFunctions Ω)
    (x : Fin N → ℝ) (c : List (Fin a) → ℝ) (q : Fin r → Nested (Fin a))
    (hI : ∀ i, wordWeight p (q i).letters ≤ s) :
    formalResidualForm (s := s) (p := p) Ω X hX u x c (fun i => wordLieElement (q i).letters) =
      wordJetResidual Ω X hX u x c (nestedResidualProduct (List.ofFn q)) := by
  rw [formalResidualForm_apply,formal_polynomial_product_nested q hI]

/-- The exact lower-factor residual hypothesis
implies symmetry of the actual formal residual on every admissible tuple. -/
theorem formalResidualForm_nested_invariant_of_lower {a s N r : ℕ} {p : Fin a → ℕ+}
    (Ω : Opens (Fin N → ℝ)) (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) (u : smoothOnFunctions Ω)
    (x : Fin N → ℝ) (c : List (Fin a) → ℝ)
    (hshort : ∀ I : List (Nested (Fin a)), I.length < r → nestedResidualWeight p I ≤ s →
      wordJetResidual Ω X hX u x c (nestedResidualProduct I) = 0)
    (q : Fin r → Nested (Fin a)) (hI : ∀ i, wordWeight p (q i).letters ≤ s)
    (hw : nestedResidualWeight p (List.ofFn q) ≤ s) (e : Equiv.Perm (Fin r)) :
    formalResidualForm (s := s) (p := p) Ω X hX u x c (fun i => wordLieElement (q (e i)).letters) =
      formalResidualForm (s := s) (p := p) Ω X hX u x c (fun i => wordLieElement (q i).letters) := by
  rw [formalResidualForm_nested Ω X hX u x c (fun i => q (e i)) (fun i => hI (e i)),
    formalResidualForm_nested Ω X hX u x c q hI]
  exact residual_nested_tuple_eq_of_perm_lower p (wordJetResidual Ω X hX u x c) hshort q hw e
end RothschildStein.L1
