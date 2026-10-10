-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.CutoffEnergyCurves
public import HeatKernel.Form.EssentialSpatialBounds
public import HeatKernel.Form.LocalEnergy
public import HeatKernel.Definitions.IsLocalWeakSolution
public import RothschildStein.Definitions.HomogeneousGroup.horizontalFields_contDiff
import Mathlib.Tactic.Linter

/-! # Energy curves of local weak parabolic solutions -/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter TopologicalSpace RothschildStein
open scoped ENNReal

namespace HeatKernel

/-- The spacetime test identity for a specified horizontal-gradient representative. -/
def SatisfiesParabolicTestIdentity {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (a : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ) (I : Opens ℝ) (U : Opens (Fin N → ℝ))
    (u : ℝ → (Fin N → ℝ) → ℝ) (g : Fin q → ℝ → (Fin N → ℝ) → ℝ) : Prop :=
  ∀ φ : ℝ × (Fin N → ℝ) → ℝ,
    ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
    tsupport φ ⊆ (I : Set ℝ) ×ˢ (U : Set (Fin N → ℝ)) →
    Integrable (fun z : ℝ × (Fin N → ℝ) =>
      -(u z.1 z.2 * fderiv ℝ φ z (1, 0)) +
        ∑ i, ∑ j, a z.1 z.2 i j * g j z.1 z.2 * fderiv ℝ φ z (0, X i z.2)) ∧
    ∫ z : ℝ × (Fin N → ℝ),
      (-(u z.1 z.2 * fderiv ℝ φ z (1, 0)) +
        ∑ i, ∑ j, a z.1 z.2 i j * g j z.1 z.2 * fderiv ℝ φ z (0, X i z.2)) = 0

/-- Local essential function bounds and square-integrable gradients on compact cylinders. -/
def HasLocalParabolicEnergyBounds {N q : ℕ} (I : Opens ℝ) (U : Opens (Fin N → ℝ))
    (u : ℝ → (Fin N → ℝ) → ℝ) (g : Fin q → ℝ → (Fin N → ℝ) → ℝ) : Prop :=
  ∀ (J : Set ℝ) (K : Set (Fin N → ℝ)),
    IsCompact J → J ⊆ (I : Set ℝ) → IsCompact K → K ⊆ (U : Set (Fin N → ℝ)) →
    essSup (fun t => eLpNorm (u t) 2 (volume.restrict K)) (volume.restrict J) < ⊤ ∧
    ∀ i, MemLp (fun z : ℝ × (Fin N → ℝ) => g i z.1 z.2) 2 (volume.restrict (J ×ˢ K))

end HeatKernel
