-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.ZeroDriftWeakWords
public import RothschildStein.H3.ZeroDriftHolderInterfaces

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal BigOperators
namespace RothschildStein.H3

/-- Transport the full global Lp regularity input and
each filtered norm sum along the literal zero-channel embedding. -/
theorem globalLpRegularity_zero_drift {N q : ℕ}
    (G : HomogeneousGroup N) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (νs : (Fin N → ℝ) → ℝ)
    (hnode : Provider.GlobalLpRegularity G driftWeight (Fin.cases 0 X)
      (fun Ω T f => hasDistributionEquationWithDrift Ω (Fin.cases 0 X)
        (fun i => (zeroDriftFields_contDiff X hX i).contDiffOn) T f) νs) :
    Provider.GlobalLpRegularity G noDriftWeight X
      (fun Ω T f => hasDistributionEquation Ω X (fun i => (hX i).contDiffOn) T f) νs := by
  intro p hp hpt
  obtain ⟨B, hB, hb⟩ := hnode p hp hpt
  refine ⟨B, hB, ?_⟩
  intro u f hu hf heq
  obtain ⟨T, hrep, hTf⟩ := heq
  obtain ⟨hs, hsecond, hfull, hfirst⟩ := hb u f hu hf
    ⟨T, hrep, (distributionEquation_zero_drift_iff ⊤ X _ _ T f).mpr hTf⟩
  exact ⟨memSobolevX_of_zero_drift X ⊤ 2 p u hs,
    (weakWordWeightSum_le_zero_drift X ⊤ 2 2 p u).trans hsecond,
    (sobolevXENorm_le_zero_drift X ⊤ 2 p u).trans hfull,
    (weakWordWeightSum_le_zero_drift X ⊤ 2 1 p u).trans hfirst⟩

/-- Transport arbitrary-distribution local
regularity and its exact full Sobolev interior estimate. -/
theorem localLpRegularity_zero_drift {N q : ℕ}
    (G : HomogeneousGroup N) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (νs : (Fin N → ℝ) → ℝ)
    (hnode : Provider.LocalLpRegularity G driftWeight (Fin.cases 0 X)
      (fun Ω T f => hasDistributionEquationWithDrift Ω (Fin.cases 0 X)
        (fun i => (zeroDriftFields_contDiff X hX i).contDiffOn) T f) νs) :
    Provider.LocalLpRegularity G noDriftWeight X
      (fun Ω T f => hasDistributionEquation Ω X (fun i => (hX i).contDiffOn) T f) νs := by
  constructor
  · intro p hp hpt Ω T f hf heq
    have hf' : memSobolevXLoc driftWeight (Fin.cases 0 X) Ω 0 p f := by
      intro U hc hs
      exact (S.memSobolevX_zero_iff _ _ U p hp.le f).mpr (hf U hc hs).1
    obtain ⟨u, hrep, hu⟩ := hnode.1 p hp hpt Ω T f hf'
      ((distributionEquation_zero_drift_iff Ω X _ _ T f).mpr heq)
    exact ⟨u, hrep, fun U hc hs => memSobolevX_of_zero_drift X U 2 p u (hu U hc hs)⟩
  · intro p hp hpt Ω A V hcA hAV hcV hVΩ
    obtain ⟨B, hB, hb⟩ := hnode.2 p hp hpt Ω A V hcA hAV hcV hVΩ
    refine ⟨B, hB, ?_⟩
    intro u f hu heq hf
    have hu' : memSobolevXLoc driftWeight (Fin.cases 0 X) Ω 2 p u :=
      fun U hc hs => (memSobolevX_zero_drift_two_iff X U p u).mpr (hu U hc hs)
    exact (sobolevXENorm_le_zero_drift X A 2 p u).trans
      (hb u f hu' ((distributionEquation_zero_drift_iff Ω X _ _ _ f).mpr heq) hf)

/-- Transport the exact bounded Lp solver,
including its fixed control ball and full norm bound. -/
theorem ballLpSolvability_zero_drift {N q : ℕ}
    (G : HomogeneousGroup N) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (νs : (Fin N → ℝ) → ℝ)
    (hnode : Provider.BallLpSolvability G driftWeight (Fin.cases 0 X)
      (fun Ω T f => hasDistributionEquationWithDrift Ω (Fin.cases 0 X)
        (fun i => (zeroDriftFields_contDiff X hX i).contDiffOn) T f) νs) :
    Provider.BallLpSolvability G noDriftWeight X
      (fun Ω T f => hasDistributionEquation Ω X (fun i => (hX i).contDiffOn) T f) νs := by
  have hd : controlDistance univ driftWeight (Fin.cases 0 X) =
      controlDistance univ noDriftWeight X := funext fun x => funext fun y =>
    controlDistance_zero_drift_eq univ X x y
  dsimp only [Provider.BallLpSolvability] at hnode ⊢
  rw [hd] at hnode
  intro p hp hpt R hR
  obtain ⟨B, hB, hb⟩ := hnode p hp hpt R hR
  refine ⟨B, hB, ?_⟩
  intro Ω hΩ f hf
  obtain ⟨u, hu, heq, hn⟩ := hb Ω hΩ f hf
  exact ⟨u, memSobolevX_of_zero_drift X Ω 2 p u hu,
    (distributionEquation_zero_drift_iff Ω X _ _ _ f).mp heq,
    (sobolevXENorm_le_zero_drift X Ω 2 p u).trans hn⟩

/-- Transport the prescribed-gauge,
scale-invariant weak norm sum without changing the radius factors. -/
theorem quasiballLpTransfer_zero_drift {N q : ℕ}
    (G : HomogeneousGroup N) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (νs : (Fin N → ℝ) → ℝ)
    (hnode : Provider.QuasiballLpTransfer G driftWeight (Fin.cases 0 X)
      (fun Ω T f => hasDistributionEquationWithDrift Ω (Fin.cases 0 X)
        (fun i => (zeroDriftFields_contDiff X hX i).contDiffOn) T f) νs) :
    Provider.QuasiballLpTransfer G noDriftWeight X
      (fun Ω T f => hasDistributionEquation Ω X (fun i => (hX i).contDiffOn) T f) νs := by
  intro p hp hpt
  obtain ⟨B, hB, hb⟩ := hnode p hp hpt
  refine ⟨B, hB, ?_⟩
  intro z r hr U V hU hV u hu
  obtain ⟨f, hf, heq, hn⟩ := hb z r hr U V hU hV u
    ((memSobolevX_zero_drift_two_iff X U p u).mpr hu)
  refine ⟨f, hf, (distributionEquation_zero_drift_iff U X _ _ _ f).mp heq, ?_⟩
  exact (add_le_add (add_le_add (weakWordWeightSum_le_zero_drift X V 2 2 p u)
    (mul_le_mul' le_rfl (weakWordWeightSum_le_zero_drift X V 2 1 p u))) le_rfl).trans hn

end RothschildStein.H3
