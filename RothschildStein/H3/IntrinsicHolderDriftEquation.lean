-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.HolderJetDriftData
public import RothschildStein.H3.WeakOperatorDistributionEquation
public import RothschildStein.H3.FrozenDriftEquationBridge
public import RothschildStein.S.IntrinsicWeakWordExport
public import RothschildStein.S.Sobolev

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal BigOperators
namespace RothschildStein.H3

/-- A compatible intrinsic Hölder jet family satisfying
its drift-plus-diagonal equation gives exactly the fixed distribution
equation. No Euclidean differentiability of the input is required. -/
theorem frozen_drift_equation_of_intrinsic_holder_jets {N q : ℕ}
    (Ω U : Opens (Fin N → ℝ)) (G : S.DistanceGeometry Ω)
    (hU : (U : Set (Fin N → ℝ)) ⊆ Ω)
    (X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (U : Set (Fin N → ℝ)))
    {α : ℝ} (hα : 0 < α) (u : (Fin N → ℝ) → ℝ)
    (jet : List (Fin (q + 1)) → (Fin N → ℝ) → ℝ) (hzero : jet [] = u)
    (hj : ∀ I, wordWeight (driftWeight (q := q)) I ≤ 2 →
      hasIntrinsicWordDeriv X U I u (jet I) ∧
      holderENorm G.d α (U : Set (Fin N → ℝ)) (jet I) < ⊤)
    (f : (Fin N → ℝ) → ℝ) (hf : ContinuousOn f (U : Set (Fin N → ℝ)))
    (heq : EqOn (fun x => jet [0] x + ∑ i : Fin q, jet [i.succ, i.succ] x)
      f (U : Set (Fin N → ℝ))) :
    hasDistributionEquationWithDrift U X hX
      (Distribution.ofFun U u volume (⊤ : ℕ∞)) f := by
  have hc (I : List (Fin (q + 1))) (hI : wordWeight (driftWeight (q := q)) I ≤ 2) :
      ContinuousOn (jet I) (U : Set (Fin N → ℝ)) :=
    S.continuousOn_of_holderENorm_lt_top_on_subset Ω G hU hα (hj I hI).2
  have hw (I : List (Fin (q + 1))) (hI : wordWeight (driftWeight (q := q)) I ≤ 2) :
      hasWeakWordDeriv X U I u (jet I) :=
    S.hasWeakWordDeriv_of_continuous_intrinsic_words U X hX I u jet hzero
      (fun J hJ => (hj J ((S.wordWeight_sublist_le driftWeight hJ).trans hI)).1)
      (fun J hJ => hc J ((S.wordWeight_sublist_le driftWeight hJ).trans hI))
  let D := holderJetDriftData Ω U G hU X hα u jet (fun I hI => ⟨hw I hI, (hj I hI).2⟩)
  have hop : D.operator =ᵐ[volume.restrict (U : Set (Fin N → ℝ))] f := by
    filter_upwards [ae_restrict_mem U.isOpen.measurableSet] with x hx
    exact heq hx
  refine ⟨hf.locallyIntegrableOn U.isOpen.measurableSet, ?_⟩
  intro ψ
  have h := D.ofFun_adjoint_equation le_top hX f hop ψ
  rw [adjointTest_zero_eq_driftTransposeTest, ← frozen_drift_transpose_test_eq] at h
  exact h

end RothschildStein.H3
