-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.LocalHolderSupNorm
public import RothschildStein.H3.WeakDriftOperatorData
public import RothschildStein.Definitions.driftWeight

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal BigOperators
namespace RothschildStein.H3

/-- The same normalized local Hölder jets define the shared
weak drift operator data at p infinity. No new representative is chosen. -/
def holderJetDriftData {N q : ℕ}
    (Ω U : Opens (Fin N → ℝ)) (G : S.DistanceGeometry Ω)
    (hU : (U : Set (Fin N → ℝ)) ⊆ Ω)
    (X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    {α : ℝ} (hα : 0 < α) (u : (Fin N → ℝ) → ℝ)
    (jet : List (Fin (q + 1)) → (Fin N → ℝ) → ℝ)
    (hj : ∀ I, wordWeight driftWeight I ≤ 2 → hasWeakWordDeriv X U I u (jet I) ∧
      holderENorm G.d α (U : Set (Fin N → ℝ)) (jet I) < ⊤) :
    WeakDriftOperatorData X U ⊤ u where
  first i := jet [i]
  square i := jet [i.succ, i.succ]
  first_weak i := (hj [i] (by by_cases hi : i = 0 <;> simp [wordWeight, driftWeight, hi])).1
  first_memLp i := memLp_top_of_local_holderNorm Ω U G hU hα
    (hj [i] (by by_cases hi : i = 0 <;> simp [wordWeight, driftWeight, hi])).2
  square_weak i := (hj [i.succ, i.succ] (by simp [wordWeight, driftWeight])).1
  square_memLp i := memLp_top_of_local_holderNorm Ω U G hU hα
    (hj [i.succ, i.succ] (by simp [wordWeight, driftWeight])).2

end RothschildStein.H3
