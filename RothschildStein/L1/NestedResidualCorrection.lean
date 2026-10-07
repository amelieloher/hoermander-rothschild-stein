-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.InvariantFormalJetCorrection
public import RothschildStein.L1.FormalResidualSymmetry
public import RothschildStein.L1.NestedProductEvaluation
public import RothschildStein.L1.WeightedNestedTuples
public import RothschildStein.L1.PolynomialSmoothTests
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.L1
open G3

/-- The lower-factor hypothesis constructs an
actual polynomial correction of every admissible r-factor residual at once. -/
theorem exists_polynomial_nested_residual_correction {a s N r : ℕ} {p : Fin a → ℕ+}
    (Ω : Opens (Fin N → ℝ)) (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) (hzero : (0 : Fin N → ℝ) ∈ Ω)
    (hf : FreeAt p s X 0) (u : smoothOnFunctions Ω) (c : List (Fin a) → ℝ)
    (hshort : ∀ I : List (Nested (Fin a)), I.length < r → nestedResidualWeight p I ≤ s →
      wordJetResidual Ω X hX u 0 c (nestedResidualProduct I) = 0) :
    ∃ (v : MvPolynomial (Fin N) ℝ)
      (hv : ContDiff ℝ (⊤ : ℕ∞) (fun x => MvPolynomial.eval x v)),
      (∀ j < r, iteratedFDeriv ℝ j (fun x => MvPolynomial.eval x v) 0 = 0) ∧
      ∀ q : Fin r → Nested (Fin a), nestedResidualWeight p (List.ofFn q) ≤ s →
        differentialPolynomialAt Ω X hX (polynomialSmoothTest Ω v hv) 0
          (nestedResidualProduct (List.ofFn q)) =
        wordJetResidual Ω X hX u 0 c (nestedResidualProduct (List.ofFn q)) := by
  obtain ⟨v,hv,hz,hvtuple⟩ := exists_polynomial_for_invariant_formal_tuples Ω X hX hzero hf
    (formalResidualForm (s := s) (p := p) (r := r) Ω X hX u 0 c)
  refine ⟨v,hv,hz,?_⟩
  intro q hw
  have hI := nested_tuple_factor_weight_le p q hw
  rw [differentialPolynomialAt_nested_product Ω X hX _ hzero q]
  change wordDerivative (fun j => wordBracket X (q j).letters)
    (List.ofFn (fun j : Fin r => j)) (fun x => MvPolynomial.eval x v) 0 = _
  rw [hvtuple (fun j => (q j).letters) hI
    (fun e => formalResidualForm_nested_invariant_of_lower Ω X hX u 0 c hshort q hI hw e)]
  exact formalResidualForm_nested Ω X hX u 0 c q hI
end RothschildStein.L1
