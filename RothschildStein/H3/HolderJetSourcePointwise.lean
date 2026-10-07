-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.HolderJetDriftData
public import RothschildStein.H3.FrozenDriftEquationBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal BigOperators
namespace RothschildStein.H3

/-- The actual fixed distribution equation identifies
its continuous selected drift source pointwise on the open domain.
The almost-everywhere bridge and shared continuity uniqueness do the work. -/
theorem holderJetSource_eqOn_of_frozen_equation {N q : ℕ}
    (Ω U : Opens (Fin N → ℝ)) (G : S.DistanceGeometry Ω)
    (hU : (U : Set (Fin N → ℝ)) ⊆ Ω)
    (X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (U : Set (Fin N → ℝ)))
    {α : ℝ} (hα : 0 < α) (u : (Fin N → ℝ) → ℝ)
    (jet : List (Fin (q + 1)) → (Fin N → ℝ) → ℝ)
    (hj : ∀ I, wordWeight driftWeight I ≤ 2 → hasWeakWordDeriv X U I u (jet I) ∧
      holderENorm G.d α (U : Set (Fin N → ℝ)) (jet I) < ⊤)
    (f : (Fin N → ℝ) → ℝ) (hf : ContinuousOn f (U : Set (Fin N → ℝ)))
    (heq : hasDistributionEquationWithDrift U X hX
      (Distribution.ofFun U u volume (⊤ : ℕ∞)) f) :
    EqOn (fun x => jet [0] x + ∑ i : Fin q, jet [i.succ, i.succ] x) f
      (U : Set (Fin N → ℝ)) := by
  let D := holderJetDriftData Ω U G hU X hα u jet hj
  have hae := D.operator_ae_eq_of_frozen_equation le_top hX f heq
  have hc (I : List (Fin (q + 1))) (hI : wordWeight driftWeight I ≤ 2) :
      ContinuousOn (jet I) (U : Set (Fin N → ℝ)) :=
    S.continuousOn_of_holderENorm_lt_top_on_subset Ω G hU hα (hj I hI).2
  have hs : ContinuousOn (fun x => jet [0] x + ∑ i : Fin q, jet [i.succ, i.succ] x)
      (U : Set (Fin N → ℝ)) :=
    (hc [0] (by simp [wordWeight, driftWeight])).add
      (continuousOn_finsetSum Finset.univ (fun i _ =>
        hc [i.succ, i.succ] (by simp [wordWeight, driftWeight])))
  exact Measure.eqOn_open_of_ae_eq hae U.isOpen hs hf

end RothschildStein.H3
