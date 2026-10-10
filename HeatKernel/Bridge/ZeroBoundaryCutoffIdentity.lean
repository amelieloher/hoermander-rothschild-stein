-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.ParabolicEnergyCurves
public import HeatKernel.Form.ZeroBoundary

/-! # Compatible bounded zero-boundary cutoff energy curves -/

@[expose] public section
open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal
namespace HeatKernel

/-- All smooth compact spatial cutoffs have bounded zero-boundary energy
curves with the specified horizontal product gradient. -/
def HasZeroBoundaryCutoffEnergyCurves {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (I : Opens ℝ) (U : Opens (Fin N → ℝ))
    (u : ℝ → (Fin N → ℝ) → ℝ) (g : Fin q → ℝ → (Fin N → ℝ) → ℝ) : Prop :=
  ∀ J : Set ℝ, IsCompact J → J ⊆ (I : Set ℝ) →
    ∀ (V : Opens (Fin N → ℝ)) (φ : (Fin N → ℝ) → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ (U : Set (Fin N → ℝ)) → tsupport φ ⊆ (V : Set (Fin N → ℝ)) →
      ∃ w : ℝ → zeroBoundaryGraph V X,
        MemLp w 2 (volume.restrict J) ∧
        essSup (fun t => eLpNorm ((w t : GradientSpace (N := N) ⊤ q).fst) 2 volume)
          (volume.restrict J) < ⊤ ∧
        (∀ᵐ t ∂volume.restrict J, (w t : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
          fun x => u t x * φ x) ∧
        ∀ i, ∀ᵐ t ∂volume.restrict J, (w t : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume]
          fun x => g i t x * φ x + u t x * fieldDerivative (X i) φ x

end HeatKernel
