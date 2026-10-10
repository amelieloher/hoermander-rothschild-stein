-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.PiecewiseCompositionContinuity
import Mathlib.Tactic.Linter

/-! # Piecewise differentiable scalar maps acting on energy curves -/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter TopologicalSpace
open scoped NNReal ENNReal

namespace HeatKernel

variable {N q : ℕ} (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {η : ℝ → ℝ} {C : ℝ≥0} (hLip : LipschitzWith C η) (hzero : η 0 = 0)
    (S : Set ℝ) (hS : S.Countable) (hη : ∀ s ∉ S, ContDiffAt ℝ 1 η s)

/-- The global energy representative of a Lipschitz composition that is locally C¹ outside a
countable set of levels and fixes zero. -/
def piecewiseEnergyComposition (u : energyGraph (N := N) ⊤ X) : energyGraph (N := N) ⊤ X :=
  Classical.choose (exists_energyGraph_comp_contDiffAt_off_countable X hX u hLip hzero S hS hη
    (d := deriv η) (fun _ _ => rfl))

/-- The scalar coordinate is the pointwise composition almost everywhere. -/
theorem piecewiseEnergyComposition_fst_ae (u : energyGraph (N := N) ⊤ X) :
    (piecewiseEnergyComposition X hX hLip hzero S hS hη u : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
      fun x => η ((u : GradientSpace (N := N) ⊤ q).fst x) :=
  (Classical.choose_spec (exists_energyGraph_comp_contDiffAt_off_countable X hX u hLip hzero S hS hη
    (d := deriv η) (fun _ _ => rfl))).1

/-- The horizontal coordinates obey the exact piecewise C¹ chain rule. -/
theorem piecewiseEnergyComposition_snd_ae (u : energyGraph (N := N) ⊤ X) (i : Fin q) :
    (piecewiseEnergyComposition X hX hLip hzero S hS hη u : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume]
      fun x => deriv η ((u : GradientSpace (N := N) ⊤ q).fst x) *
        (u : GradientSpace (N := N) ⊤ q).snd i x :=
  (Classical.choose_spec (exists_energyGraph_comp_contDiffAt_off_countable X hX u hLip hzero S hS hη
    (d := deriv η) (fun _ _ => rfl))).2.1 i

/-- Piecewise C¹ scalar composition is continuous for the horizontal graph norm. -/
theorem continuous_piecewiseEnergyComposition :
    Continuous (piecewiseEnergyComposition X hX hLip hzero S hS hη) :=
  continuous_energyGraph_composition_off_countable X hX hLip hzero S hS hη _
    (piecewiseEnergyComposition_fst_ae X hX hLip hzero S hS hη)
    (piecewiseEnergyComposition_snd_ae X hX hLip hzero S hS hη)

/-- The scalar Lipschitz bound controls the full graph norm of the composition. -/
theorem norm_piecewiseEnergyComposition_le (u : energyGraph (N := N) ⊤ X) :
    ‖piecewiseEnergyComposition X hX hLip hzero S hS hη u‖ ≤ (C : ℝ) * ‖u‖ :=
  (Classical.choose_spec (exists_energyGraph_comp_contDiffAt_off_countable X hX u hLip hzero S hS hη
    (d := deriv η) (fun _ _ => rfl))).2.2

end HeatKernel
