-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.DistributionWords
public import RothschildStein.Definitions.sumSquaresWithDriftTranspose

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open TopologicalSpace
open scoped BigOperators

/-- The fixed drift transpose preserves compact smooth tests. -/
def driftTransposeTest {n q : ℕ}
    (Ω : Opens (Fin n → ℝ))
    (X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (ψ : TestFunction Ω ℝ (⊤ : ℕ∞)) : TestFunction Ω ℝ (⊤ : ℕ∞) :=
  wordTransposeTest Ω X hX [0] ψ +
    ∑ i : Fin q, wordTransposeTest Ω X hX [i.succ,i.succ] ψ

/-- Evaluation agrees with the exact fixed drift transpose. -/
theorem driftTransposeTest_apply {n q : ℕ}
    (Ω : Opens (Fin n → ℝ))
    (X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (ψ : TestFunction Ω ℝ (⊤ : ℕ∞)) (x : Fin n → ℝ) :
    driftTransposeTest Ω X hX ψ x = sumSquaresWithDriftTranspose X ψ x := by
  simp [driftTransposeTest, S.wordTransposeTest_apply, wordTranspose,
    sumSquaresWithDriftTranspose]

end RothschildStein.H3
