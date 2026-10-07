-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.NestedProductEvaluation
public import RothschildStein.L1.PolynomialSmoothTests
public import RothschildStein.L1.LeadingWordJets
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.L1
open G3

/-- A polynomial correction with zero lower jets
vanishes on every shorter nested commutator product, with no weight restriction. -/
theorem differentialPolynomialAt_nested_zero_of_lower_jets {a N r : ℕ}
    (Ω : Opens (Fin N → ℝ)) (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) (hzero : (0 : Fin N → ℝ) ∈ Ω)
    (v : MvPolynomial (Fin N) ℝ)
    (hv : ContDiff ℝ (⊤ : ℕ∞) (fun x => MvPolynomial.eval x v))
    (hz : ∀ j < r, iteratedFDeriv ℝ j (fun x => MvPolynomial.eval x v) 0 = 0)
    (I : List (Nested (Fin a))) (hlen : I.length < r) :
    differentialPolynomialAt Ω X hX (polynomialSmoothTest Ω v hv) 0 (nestedResidualProduct I) = 0 := by
  have he := differentialPolynomialAt_nested_product Ω X hX (polynomialSmoothTest Ω v hv) hzero I.get
  rw [List.ofFn_get] at he
  rw [he]
  apply wordDerivative_zero_of_lower_jets_on Ω _
    (fun j => G1.wordBracket_contDiffOn Ω.isOpen X hX (I.get j).letters) _ hv.contDiffOn hzero
    (List.ofFn (fun j : Fin I.length => j)) (by simpa using hlen) hz
end RothschildStein.L1
