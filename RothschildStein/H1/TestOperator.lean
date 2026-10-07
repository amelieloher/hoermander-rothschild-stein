-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.OperatorAlgebra
public import RothschildStein.S.ClassicalWords

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped BigOperators
namespace RothschildStein.H1
variable {N q : ℕ}

/-- Realization of the sum of squares with its chosen drift on
smooth compact tests, reusing the S word API (BB pp. 250, 256–257). -/
def sumSquaresTest (Ω : Opens (Fin N → ℝ))
    (X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin N → ℝ)))
    (φ : TestFunction Ω ℝ (⊤ : ℕ∞)) : TestFunction Ω ℝ (⊤ : ℕ∞) :=
  S.wordDerivativeTest Ω X hX [0] φ +
    ∑ i : Fin q, S.wordDerivativeTest Ω X hX [i.succ, i.succ] φ

/-- The realization is the field operator (BB p. 250). -/
theorem sumSquaresTest_apply (Ω : Opens (Fin N → ℝ))
    (X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin N → ℝ)))
    (φ : TestFunction Ω ℝ (⊤ : ℕ∞)) (x : Fin N → ℝ) :
    sumSquaresTest Ω X hX φ x = sumSquaresWithDrift X φ x := by
  simp [sumSquaresTest, S.wordDerivativeTest, wordDerivative, sumSquaresWithDrift]

/-- The true test operator has a linear bounded-continuous
realization for Hahn–Banach (BB Prop 6.2, p. 250). -/
def sumSquaresBoundedTest (Ω : Opens (Fin N → ℝ))
    (X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin N → ℝ))) :
    TestFunction Ω ℝ (⊤ : ℕ∞) →ₗ[ℝ] BoundedContinuousFunction (Fin N → ℝ) ℝ where
  toFun φ := (TestFunction.toBoundedContinuousFunctionCLM ℝ) (sumSquaresTest Ω X hX φ)
  map_add' φ ψ := by
    ext x
    change sumSquaresTest Ω X hX (φ + ψ) x =
      sumSquaresTest Ω X hX φ x + sumSquaresTest Ω X hX ψ x
    by_cases hx : x ∈ Ω
    · simp only [sumSquaresTest_apply]
      exact sumSquares_add_at (φ.contDiff.of_le (by simp)).contDiffAt
        (ψ.contDiff.of_le (by simp)).contDiffAt
        (fun i => ((hX i.succ).contDiffAt (Ω.isOpen.mem_nhds hx)).differentiableAt (by simp))
    · rw [(sumSquaresTest Ω X hX (φ + ψ)).zero_on_compl hx,
        (sumSquaresTest Ω X hX φ).zero_on_compl hx,
        (sumSquaresTest Ω X hX ψ).zero_on_compl hx]
      simp only [Pi.zero_apply, zero_add]
  map_smul' c φ := by
    ext x
    change sumSquaresTest Ω X hX (c • φ) x = c * sumSquaresTest Ω X hX φ x
    simp only [sumSquaresTest_apply]
    exact congrFun (sumSquares_const_mul X c φ) x

/-- The linear realization retains the field action at every point
(BB p. 250). -/
theorem sumSquaresBoundedTest_apply (Ω : Opens (Fin N → ℝ))
    (X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin N → ℝ)))
    (φ : TestFunction Ω ℝ (⊤ : ℕ∞)) (x : Fin N → ℝ) :
    sumSquaresBoundedTest Ω X hX φ x = sumSquaresWithDrift X φ x :=
  sumSquaresTest_apply Ω X hX φ x

end RothschildStein.H1
