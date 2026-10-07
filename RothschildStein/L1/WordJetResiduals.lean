-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.AssociativeResiduals
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.L1

/-- The prescribed ordered word jets define a
linear functional on the entire associative polynomial algebra. -/
def wordJetFunctional {a : ℕ} (c : List (Fin a) → ℝ) :
    MonoidAlgebra ℝ (FreeMonoid (Fin a)) →ₗ[ℝ] ℝ :=
  (Finsupp.linearCombination ℝ (fun I : FreeMonoid (Fin a) => c I.toList)).comp
    (MonoidAlgebra.coeffLinearEquiv ℝ).toLinearMap

/-- The word functional returns the prescribed coefficient at each word. -/
theorem wordJetFunctional_single {a : ℕ} (c : List (Fin a) → ℝ) (I : List (Fin a)) :
    wordJetFunctional c (MonoidAlgebra.single (FreeMonoid.ofList I) 1) = c I := by
  change Finsupp.linearCombination ℝ (fun w : FreeMonoid (Fin a) => c w.toList)
    (MonoidAlgebra.single (FreeMonoid.ofList I) 1).coeff = c I
  rw [MonoidAlgebra.coeff_single,Finsupp.linearCombination_single]
  simp

/-- The actual residual functional in the source's induction. -/
def wordJetResidual {a N : ℕ} (Ω : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (u : G3.smoothOnFunctions Ω) (x : Fin N → ℝ) (c : List (Fin a) → ℝ) :
    MonoidAlgebra ℝ (FreeMonoid (Fin a)) →ₗ[ℝ] ℝ :=
  wordJetFunctional c - differentialPolynomialAt Ω X hX u x

/-- The residual on an ordered monomial is exactly
the prescribed jet minus the actual ordered derivative. -/
theorem wordJetResidual_single {a N : ℕ} (Ω : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (u : G3.smoothOnFunctions Ω) {x : Fin N → ℝ} (hx : x ∈ Ω)
    (c : List (Fin a) → ℝ) (I : List (Fin a)) :
    wordJetResidual Ω X hX u x c (MonoidAlgebra.single (FreeMonoid.ofList I) 1) =
      c I - wordDerivative X I u.val x := by
  change wordJetFunctional c _ - differentialPolynomialAt Ω X hX u x _ = _
  rw [wordJetFunctional_single]
  change c I - (G3.differentialWordEvaluation Ω X hX
    (MonoidAlgebra.single (FreeMonoid.ofList I) 1) u).val x = _
  rw [G3.differentialWordEvaluation_single Ω X hX I 1 u hx,one_mul]
end RothschildStein.L1
