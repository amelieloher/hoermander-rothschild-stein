-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.HolderJetDriftData
public import RothschildStein.H3.FirstHolderNormFormula
public import RothschildStein.S.WeakIntrinsicWords
public import RothschildStein.S.Sobolev

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal BigOperators
namespace RothschildStein.H3

/-- The local normalized continuous weak jets control the
horizontal L infinity sum by the exact fixed full first-order norm. -/
theorem first_weakJetNorm_sum_le_holderX {N q : ℕ}
    (Ω U : Opens (Fin N → ℝ)) (G : S.DistanceGeometry Ω)
    (hU : (U : Set (Fin N → ℝ)) ⊆ Ω)
    (X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (U : Set (Fin N → ℝ)))
    {α : ℝ} (hα : 0 < α) (u : (Fin N → ℝ) → ℝ)
    (jet : List (Fin (q + 1)) → (Fin N → ℝ) → ℝ)
    (hzero : jet [] = u)
    (hj : ∀ I, wordWeight driftWeight I ≤ 2 → hasWeakWordDeriv X U I u (jet I) ∧
      holderENorm G.d α (U : Set (Fin N → ℝ)) (jet I) < ⊤) :
    (∑ i : Fin q, weakWordENorm X U [i.succ] ⊤ u) ≤
      holderXENorm driftWeight X G.d U 1 α u := by
  have hi (i : Fin q) : hasIntrinsicWordDeriv X U [i.succ] u (jet [i.succ]) := by
    apply S.hasIntrinsicWordDeriv_of_continuous_weak_subwords U X hX
      [i.succ] u jet hzero
    · intro J hJ
      exact (hj J ((S.wordWeight_sublist_le driftWeight hJ).trans
        (by simp [wordWeight, driftWeight]))).1
    · intro J hJ
      exact S.continuousOn_of_holderENorm_lt_top_subset Ω G hU hα
        (hj J ((S.wordWeight_sublist_le driftWeight hJ).trans
          (by simp [wordWeight, driftWeight]))).2
  rw [holderXENorm_drift_one_eq X G.d U α u (fun i => jet [i.succ]) hi]
  apply le_trans _ (le_add_left le_rfl)
  apply Finset.sum_le_sum
  intro i _
  rw [S.weakWordENorm_eq X U [i.succ] ⊤ u (jet [i.succ])
    (hj _ (by simp [wordWeight, driftWeight])).1]
  exact eLpNorm_top_le_local_holderNorm Ω U G hU hα
    (hj _ (by simp [wordWeight, driftWeight])).2

end RothschildStein.H3
