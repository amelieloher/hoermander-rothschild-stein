-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.FirstHolderNormFormula
public import RothschildStein.S.WeakIntrinsicWords
public import RothschildStein.S.HolderSubsetContinuity

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped ENNReal
namespace RothschildStein.H3

/-- Normalized weak Hölder jets realize the complete first-order
intrinsic norm. Continuity and the intrinsic representatives are derived
from the actual weak jets, with no derivative identity assumed. -/
theorem holderXENorm_drift_one_eq_of_weak_jets {N q : ℕ}
    (Ω U : Opens (Fin N → ℝ)) (D : S.DistanceGeometry Ω)
    (hU : (U : Set (Fin N → ℝ)) ⊆ Ω)
    (X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (U : Set (Fin N → ℝ)))
    {a : ℝ} (ha : 0 < a) (u : (Fin N → ℝ) → ℝ)
    (jet : List (Fin (q + 1)) → (Fin N → ℝ) → ℝ) (hz : jet [] = u)
    (hj : ∀ I, wordWeight driftWeight I ≤ 1 → hasWeakWordDeriv X U I u (jet I) ∧
      holderENorm D.d a (U : Set (Fin N → ℝ)) (jet I) < ⊤) :
    holderXENorm driftWeight X D.d U 1 a u =
      holderENorm D.d a (U : Set (Fin N → ℝ)) u +
        ∑ i : Fin q, holderENorm D.d a (U : Set (Fin N → ℝ)) (jet [i.succ]) := by
  apply holderXENorm_drift_one_eq X D.d U a u (fun i => jet [i.succ])
  intro i
  apply S.hasIntrinsicWordDeriv_of_continuous_weak_subwords U X hX [i.succ] u jet hz
  · intro J hJ
    exact (hj J ((S.wordWeight_sublist_le driftWeight hJ).trans
      (by simp [wordWeight, driftWeight]))).1
  · intro J hJ
    exact S.continuousOn_of_holderENorm_lt_top_subset Ω D hU ha
      (hj J ((S.wordWeight_sublist_le driftWeight hJ).trans
        (by simp [wordWeight, driftWeight]))).2

end RothschildStein.H3
