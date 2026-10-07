-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.ZeroDriftHolderMembership
public import RothschildStein.H3.ZeroDriftDistributionEquation
public import RothschildStein.H3.LocalHolderGeometryContinuity
public import RothschildStein.S.HolderZeroOrder
public import RothschildStein.Provider.GroupRegularityInputs

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped ENNReal
namespace RothschildStein.H3

/-- Smoothness of the shifted frame, including its zero drift. -/
theorem zeroDriftFields_contDiff {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (i : Fin (q + 1)) :
    ContDiff ℝ (⊤ : ℕ∞) (Fin.cases 0 X i) := by
  cases i using Fin.cases with
  | zero => exact contDiff_const
  | succ i => exact hX i

/-- Transport the global Holder estimate to arbitrary distributions with
the full intrinsic norm. -/
theorem localHolderRegularity_zero_drift {N q : ℕ}
    (G : HomogeneousGroup N) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (νs : (Fin N → ℝ) → ℝ)
    (D : S.DistanceGeometry (⊤ : Opens (Fin N → ℝ)))
    (hD : D.d = controlDistance univ noDriftWeight X)
    (hnode : Provider.LocalHolderRegularity G driftWeight (Fin.cases 0 X)
      (fun Ω T f => hasDistributionEquationWithDrift Ω (Fin.cases 0 X)
        (fun i => (zeroDriftFields_contDiff X hX i).contDiffOn) T f) νs) :
    Provider.LocalHolderRegularity G noDriftWeight X
      (fun Ω T f => hasDistributionEquation Ω X (fun i => (hX i).contDiffOn) T f) νs := by
  have hd : controlDistance univ driftWeight (Fin.cases 0 X) =
      controlDistance univ noDriftWeight X := funext fun x => funext fun y =>
    controlDistance_zero_drift_eq univ X x y
  dsimp only [Provider.LocalHolderRegularity] at hnode ⊢
  rw [hd] at hnode
  refine ⟨?_, ?_⟩
  · intro α ha ha1 Ω T f hf heq
    have hf' : memHolderXLoc driftWeight (Fin.cases 0 X)
        (controlDistance univ noDriftWeight X) Ω 0 α f := by
      intro U hc hs
      exact (S.memHolderX_zero_iff _ _ _ _ _ _).mpr (hf U hc hs).1
    obtain ⟨u, hrep, hu⟩ := hnode.1 α ha ha1 Ω T f hf'
      ((distributionEquation_zero_drift_iff Ω X _ _ T f).mpr heq)
    exact ⟨u, hrep, fun U hc hs => memHolderX_of_zero_drift X _ U 2 α u (hu U hc hs)⟩
  · intro α ha ha1 Ω A V hcA hAV hcV hVΩ
    obtain ⟨B, hB, hb⟩ := hnode.2 α ha ha1 Ω A V hcA hAV hcV hVΩ
    refine ⟨B, hB, ?_⟩
    intro u f hu heq hf
    have huD : memHolderXLoc noDriftWeight X D.d Ω 2 α u := by simpa only [hD] using hu
    have hcont := continuousOn_of_memHolderXLoc_with_geometry noDriftWeight X D Ω 2 ha huD
    have hu' : memHolderXLoc driftWeight (Fin.cases 0 X)
        (controlDistance univ noDriftWeight X) Ω 2 α u := by
      intro U hc hs
      exact (memHolderX_zero_drift_two_iff X _ U α u
        (hcont.mono (subset_closure.trans hs))).mpr (hu U hc hs)
    have hn := hb u f hu' ((distributionEquation_zero_drift_iff Ω X _ _ _ f).mpr heq) hf
    exact (holderXENorm_le_zero_drift X _ A 2 α u).trans hn

/-- Transport the enlarged-ball solver,
preserving its prescribed gauge, full norm and constant quantifiers. -/
theorem holderBallTransfer_zero_drift {N q : ℕ}
    (G : HomogeneousGroup N) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (νs : (Fin N → ℝ) → ℝ)
    (hnode : Provider.HolderBallTransfer G driftWeight (Fin.cases 0 X)
      (fun Ω T f => hasDistributionEquationWithDrift Ω (Fin.cases 0 X)
        (fun i => (zeroDriftFields_contDiff X hX i).contDiffOn) T f) νs) :
    Provider.HolderBallTransfer G noDriftWeight X
      (fun Ω T f => hasDistributionEquation Ω X (fun i => (hX i).contDiffOn) T f) νs := by
  have hd : controlDistance univ driftWeight (Fin.cases 0 X) =
      controlDistance univ noDriftWeight X := funext fun x => funext fun y =>
    controlDistance_zero_drift_eq univ X x y
  dsimp only [Provider.HolderBallTransfer] at hnode ⊢
  rw [hd] at hnode
  intro α ha ha1 R hR
  obtain ⟨S, hS, V, hV, hcontains, B, hB, hb⟩ := hnode α ha ha1 R hR
  refine ⟨S, hS, V, hV, hcontains, B, hB, ?_⟩
  intro Ω hΩ f hf hzero
  have hf' : memHolderXCompact driftWeight (Fin.cases 0 X)
      (controlDistance univ noDriftWeight X) Ω 0 α f :=
    ⟨(RothschildStein.S.memHolderX_zero_iff _ _ _ _ _ _).mpr hf.1.1, hf.2⟩
  obtain ⟨u, hu, heq, hn⟩ := hb Ω hΩ f hf' hzero
  exact ⟨u, memHolderX_of_zero_drift X _ V 2 α u hu,
    (distributionEquation_zero_drift_iff V X _ _ _ f).mp heq,
    (holderXENorm_le_zero_drift X _ V 2 α u).trans hn⟩

end RothschildStein.H3
