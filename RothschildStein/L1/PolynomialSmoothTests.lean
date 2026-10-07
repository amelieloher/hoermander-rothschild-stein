-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.WordJetResiduals
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.L1

/-- An actual polynomial bundled on the coefficient domain. -/
def polynomialSmoothTest {N : ℕ} (Ω : Opens (Fin N → ℝ)) (u : MvPolynomial (Fin N) ℝ)
    (hu : ContDiff ℝ (⊤ : ℕ∞) (fun x => MvPolynomial.eval x u)) : G3.smoothOnFunctions Ω :=
  ⟨fun x => MvPolynomial.eval x u,hu.contDiffOn⟩

/-- Differential polynomial evaluation is linear in the test function. -/
theorem differentialPolynomialAt_test_add {a N : ℕ} (Ω : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (u v : G3.smoothOnFunctions Ω) (x : Fin N → ℝ)
    (P : MonoidAlgebra ℝ (FreeMonoid (Fin a))) :
    differentialPolynomialAt Ω X hX (u+v) x P =
      differentialPolynomialAt Ω X hX u x P + differentialPolynomialAt Ω X hX v x P := by
  change (G3.differentialWordEvaluation Ω X hX P (u+v)).val x = _
  rw [map_add]
  rfl

/-- Adding a correction subtracts its actual
ordered differential polynomial value from the previous residual. -/
theorem wordJetResidual_test_add {a N : ℕ} (Ω : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (u v : G3.smoothOnFunctions Ω) (x : Fin N → ℝ) (c : List (Fin a) → ℝ)
    (P : MonoidAlgebra ℝ (FreeMonoid (Fin a))) :
    wordJetResidual Ω X hX (u+v) x c P =
      wordJetResidual Ω X hX u x c P - differentialPolynomialAt Ω X hX v x P := by
  change wordJetFunctional c P - differentialPolynomialAt Ω X hX (u+v) x P = _
  rw [differentialPolynomialAt_test_add]
  change _ = (wordJetFunctional c P - differentialPolynomialAt Ω X hX u x P) - _
  ring
end RothschildStein.L1
