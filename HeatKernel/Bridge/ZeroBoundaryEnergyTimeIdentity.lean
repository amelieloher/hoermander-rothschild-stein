-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Bridge.CutoffEnergyTimeIdentity
public import HeatKernel.Bridge.ZeroBoundaryValueFunctional

/-! # Zero-boundary cutoff energy curves and their dual time equations -/

@[expose] public section
open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal
namespace HeatKernel

/-- A cutoff energy curve with its specified value and horizontal gradient,
local essential spatial bound, and square-integrable dual time flux. -/
def IsZeroBoundaryCutoffEnergyTimePair {N q : ℕ} (V : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (a : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ) (J : Set ℝ)
    (u : ℝ → (Fin N → ℝ) → ℝ) (g : Fin q → ℝ → (Fin N → ℝ) → ℝ)
    (φ : (Fin N → ℝ) → ℝ) (v : ℝ → zeroBoundaryGraph V X)
    (F : ℝ → (zeroBoundaryGraph V X →L[ℝ] ℝ)) : Prop :=
  MemLp v 2 (volume.restrict J) ∧
    essSup (fun t => eLpNorm ((v t : GradientSpace (N := N) ⊤ q).fst) 2 volume)
      (volume.restrict J) < ⊤ ∧
    (∀ᵐ t ∂volume.restrict J, (v t : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
      fun x => u t x * φ x) ∧
    (∀ i, ∀ᵐ t ∂volume.restrict J, (v t : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume]
      fun x => g i t x * φ x + u t x * fieldDerivative (X i) φ x) ∧
    MemLp F 2 (volume.restrict J) ∧
    (∀ᵐ t ∂volume.restrict J, ∀ w : zeroBoundaryGraph V X,
      F t w = ∑ i, ∫ x, (∑ j, a t x i j * g j t x) *
        (φ x * (w : GradientSpace (N := N) ⊤ q).snd i x +
          fieldDerivative (X i) φ x * (w : GradientSpace (N := N) ⊤ q).fst x)) ∧
    SatisfiesDualTimeBalance J
      (fun t => zeroBoundaryValueFunctional V X (v t)) F

/-- Every interior smooth spatial cutoff has a compatible energy curve and dual
flux on each compact interior time set. -/
def HasZeroBoundaryCutoffEnergyTimeCurves {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (a : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ)
    (I : Opens ℝ) (U : Opens (Fin N → ℝ))
    (u : ℝ → (Fin N → ℝ) → ℝ) (g : Fin q → ℝ → (Fin N → ℝ) → ℝ) : Prop :=
  ∀ J : Set ℝ, IsCompact J → J ⊆ (I : Set ℝ) →
    ∀ (V : Opens (Fin N → ℝ)) (φ : (Fin N → ℝ) → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ (U : Set (Fin N → ℝ)) → tsupport φ ⊆ (V : Set (Fin N → ℝ)) →
      ∃ (v : ℝ → zeroBoundaryGraph V X)
        (F : ℝ → (zeroBoundaryGraph V X →L[ℝ] ℝ)),
        IsZeroBoundaryCutoffEnergyTimePair V X a J u g φ v F

end HeatKernel
