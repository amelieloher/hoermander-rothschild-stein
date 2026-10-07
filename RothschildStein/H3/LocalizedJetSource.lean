-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.CutoffContinuousIntrinsicJets
public import RothschildStein.Definitions.sumSquaresWithDrift

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open scoped BigOperators
namespace RothschildStein.H3

/-- The actual ordered cutoff jets give the localized drift
source, with both copies of each horizontal cross term. -/
theorem localized_jet_source {N q : ℕ}
    (X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (u φ : (Fin N → ℝ) → ℝ)
    (jet : List (Fin (q + 1)) → (Fin N → ℝ) → ℝ)
    (hzero : jet [] = u) (x : Fin N → ℝ) :
    S.leibnizWordValue X [0] jet φ x +
      ∑ i : Fin q, S.leibnizWordValue X [i.succ, i.succ] jet φ x =
    φ x * (jet [0] x + ∑ i : Fin q, jet [i.succ, i.succ] x) +
      2 * (∑ i : Fin q, fieldDerivative (X i.succ) φ x * jet [i.succ] x) +
      u x * sumSquaresWithDrift X φ x := by
  simp only [S.leibnizWordValue, S.leibnizSplits, List.map_cons, List.map_nil,
    List.map_append, List.sum_cons, List.sum_nil, List.sum_append,
    wordDerivative, hzero, sumSquaresWithDrift, add_zero]
  simp only [Finset.sum_add_distrib]
  simp only [← Finset.mul_sum, mul_comm]
  ring

end RothschildStein.H3
