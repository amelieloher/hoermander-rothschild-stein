-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.IntrinsicWeakDerivative
public import RothschildStein.S.IntrinsicWeakWordsConditional

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.S
variable {n q : ℕ}

/-- Continuous intrinsic representatives for all subwords determine the weak word derivative (BB pp. 87–90). -/
theorem hasWeakWordDeriv_of_continuous_intrinsic_words
    (Ω : Opens (Fin n → ℝ))
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i,ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (I : List (Fin q)) (f : (Fin n → ℝ) → ℝ)
    (jet : List (Fin q) → (Fin n → ℝ) → ℝ) (hzero : jet [] = f)
    (hi : ∀ J,J.Sublist I → hasIntrinsicWordDeriv X Ω J f (jet J))
    (hc : ∀ J,J.Sublist I → ContinuousOn (jet J) (Ω : Set (Fin n → ℝ))) :
    hasWeakWordDeriv X Ω I f (jet I) :=
  hasWeakWordDeriv_of_intrinsicToWeak hasWeakWordDeriv_of_intrinsic_derivative
    Ω X hX I f jet hzero hi hc

end RothschildStein.S
