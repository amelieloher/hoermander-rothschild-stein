-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.EnergyDensity
public import HeatKernel.Form.LocalEnergy

import Mathlib.Tactic.Linter

/-! # Strong locality of the horizontal energy form -/

@[expose] public section

noncomputable section

open Set MeasureTheory TopologicalSpace RothschildStein

namespace HeatKernel

/-- An energy-domain function constant on an open set has zero horizontal gradient there. -/
theorem energyGraph_gradient_zero_on_of_fst_const {N q : ℕ}
    (U : Opens (Fin N → ℝ)) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (u : energyGraph (N := N) ⊤ X)
    (c : ℝ) (hu : (u : GradientSpace (N := N) ⊤ q).fst
      =ᵐ[volume.restrict (U : Set (Fin N → ℝ))] (fun _ => c)) (i : Fin q) :
    (u : GradientSpace (N := N) ⊤ q).snd i
      =ᵐ[volume.restrict (U : Set (Fin N → ℝ))] (fun _ => 0) := by
  have hweak := energyGraph_le_weakGradientGraph ⊤ X (fun j => (hX j).contDiffOn) u.property i
  have hU := S.hasWeakWordDeriv_restrict X ⊤ U (subset_univ _) hweak
  have hconst : hasWeakWordDeriv X U [i] (fun _ => c) (fun _ => 0) := by
    have hd : wordDerivative X [i] (fun _ => c) = (fun _ => 0) := by
      funext x
      simp only [wordDerivative, fieldDerivative, fderiv_const_apply, zero_apply]
    simpa only [hd] using S.hasWeakWordDeriv_classical U X
      (fun j => (hX j).contDiffOn) [i] (fun _ => c) contDiffOn_const
  exact S.hasWeakWordDeriv_unique X U
    (S.hasWeakWordDeriv_congr_ae X U hU hu Filter.EventuallyEq.rfl) hconst

end HeatKernel
