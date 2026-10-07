-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.NestedResidualProducts
public import RothschildStein.G3.BracketPolynomialCoefficients
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.L1
open G3

/-- Full associative commutator products act as
the actual ordered products of nested field operators on the open domain. -/
theorem differentialPolynomialAt_nested_product {a N r : ℕ}
    (Ω : Opens (Fin N → ℝ)) (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) (u : smoothOnFunctions Ω)
    {x : Fin N → ℝ} (hx : x ∈ Ω) (q : Fin r → Nested (Fin a)) :
    differentialPolynomialAt Ω X hX u x (nestedResidualProduct (List.ofFn q)) =
      wordDerivative (fun j => wordBracket X (q j).letters) (List.ofFn (fun j : Fin r => j)) u.val x := by
  let Y := fun j => wordBracket X (q j).letters
  have hY : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (Y j) Ω :=
    fun j => G1.wordBracket_contDiffOn Ω.isOpen X hX (q j).letters
  have he : differentialWordEvaluation Ω X hX (nestedResidualProduct (List.ofFn q)) =
      FreeMonoid.lift (fun j => smoothFieldOperator Ω (Y j) (hY j))
        (FreeMonoid.ofList (List.ofFn (fun j : Fin r => j))) := by
    rw [nestedResidualProduct,map_list_prod,FreeMonoid.lift_ofList]
    simp only [List.map_ofFn,Function.comp_def]
    apply congrArg (fun f : Fin r → Module.End ℝ (smoothOnFunctions Ω) => (List.ofFn f).prod)
    funext j
    exact differentialWordEvaluation_bracketWord Ω X hX (q j).letters (Nested.letters_ne_nil (q j))
  change (differentialWordEvaluation Ω X hX (nestedResidualProduct (List.ofFn q)) u).val x = _
  rw [he]
  exact differentialWordEvaluation_word Ω Y hY _ u hx
end RothschildStein.L1
