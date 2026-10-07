-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Definitions.wordDerivative
public import RothschildStein.Definitions.sumSquaresWithDrift

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open scoped BigOperators

/-- The fixed drift operator is the sum of its drift and square words. -/
theorem sumSquaresWithDrift_eq_word_sum {n q : ℕ}
    (X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ)) (u : (Fin n → ℝ) → ℝ) :
    sumSquaresWithDrift X u =
      wordDerivative X [0] u + ∑ i : Fin q, wordDerivative X [i.succ,i.succ] u := by
  funext x
  simp only [sumSquaresWithDrift,wordDerivative,Pi.add_apply,Finset.sum_apply]

end RothschildStein.H3
