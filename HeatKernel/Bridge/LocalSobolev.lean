-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.GraphForm
public import HeatKernel.Form.LocalEnergyIdentification
public import HeatKernel.Moser.LocalHorizontalDerivatives
public import RothschildStein.H3.LocalSobolevIntegrability
import Mathlib.Tactic.Linter
import Mathlib.Tactic.NormNum

/-! # Equivalence of local horizontal form and weak Sobolev membership

Local energy representatives give square-integrable weak derivatives on every
relatively compact open set. Conversely, local weak Sobolev functions have
local energy representatives by smooth interior cutoff approximation.
-/

@[expose] public section
open Set MeasureTheory TopologicalSpace RothschildStein
namespace HeatKernel

/-- Local closed-form representatives give literal local horizontal Sobolev membership. -/
theorem MemLocalEnergy.memSobolevXLoc {N q : ℕ} {U : Opens (Fin N → ℝ)}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) {f : (Fin N → ℝ) → ℝ}
    (hf : MemLocalEnergy U X f) : memSobolevXLoc noDriftWeight X U 1 2 f := by
  intro V hVc hVU
  obtain ⟨w, hw⟩ := hf.2 V hVc hVU
  have hfp : MemLp ((w : GradientSpace (N := N) ⊤ q).fst : (Fin N → ℝ) → ℝ) 2 volume := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      Lp.memLp (w : GradientSpace (N := N) ⊤ q).fst
  apply memSobolevX_noDrift_one_two_iff.mpr
  refine ⟨(hfp.restrict _).ae_eq hw, fun i => ?_⟩
  refine ⟨(w : GradientSpace (N := N) ⊤ q).snd i, ?_, ?_⟩
  · have hweak := energyGraph_le_weakGradientGraph ⊤ X
      (fun j => (hX j).contDiffOn) w.property i
    exact S.hasWeakWordDeriv_congr_ae X V
      (S.hasWeakWordDeriv_restrict X ⊤ V (subset_univ _) hweak)
      hw Filter.EventuallyEq.rfl
  · have hgp : MemLp ((w : GradientSpace (N := N) ⊤ q).snd i : (Fin N → ℝ) → ℝ) 2 volume := by
      simpa only [Opens.coe_top, Measure.restrict_univ] using
        Lp.memLp ((w : GradientSpace (N := N) ⊤ q).snd i)
    exact hgp.restrict _

/-- The local form and literal weak Sobolev domains agree. -/
theorem memLocalEnergy_iff_memSobolevXLoc {N q : ℕ} (U : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) {f : (Fin N → ℝ) → ℝ} :
    MemLocalEnergy U X f ↔ memSobolevXLoc noDriftWeight X U 1 2 f := by
  constructor
  · exact fun hf => hf.memSobolevXLoc hX
  · intro hf
    have hm := (H3.locallyIntegrableOn_of_memSobolevXLoc noDriftWeight X U 1 2
      (by norm_num) hf).aestronglyMeasurable
    exact memLocalEnergy_of_memSobolevXLoc U X hX hm hf

/-- A separately supplied weak gradient agrees with every local form representative. -/
theorem energyGradient_eq_of_local_weak_derivative {N q : ℕ}
    (U V : Opens (Fin N → ℝ)) (hVU : (V : Set (Fin N → ℝ)) ⊆ U)
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (w : energyGraph (N := N) ⊤ X) {f g : (Fin N → ℝ) → ℝ}
    (hw : (w : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume.restrict (V : Set (Fin N → ℝ))] f)
    (i : Fin q) (hg : hasWeakWordDeriv X U [i] f g) :
    energyGradient ⊤ X w i =ᵐ[volume.restrict (V : Set (Fin N → ℝ))] g := by
  have hweak := energyGraph_le_weakGradientGraph ⊤ X
    (fun j => (hX j).contDiffOn) w.property i
  exact S.hasWeakWordDeriv_unique X V
    (S.hasWeakWordDeriv_congr_ae X V
      (S.hasWeakWordDeriv_restrict X ⊤ V (subset_univ _) hweak)
      hw Filter.EventuallyEq.rfl)
    (S.hasWeakWordDeriv_restrict X U V hVU hg)

end HeatKernel
