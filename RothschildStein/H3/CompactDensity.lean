-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.LocalSecondWord

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory TopologicalSpace
open scoped ENNReal BigOperators

/-- The local second-word bound uses the compact second-order estimate
and global Sobolev density. -/
theorem local_second_word_of_compact_and_density {n q : ℕ}
    (X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (p : ℝ≥0∞) (hp : 1 ≤ p) (C : ℝ)
    (hcompact : ∀ v : (Fin n → ℝ) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) v → HasCompactSupport v →
      ∀ I : List (Fin (q+1)), wordWeight driftWeight I = 2 →
        eLpNorm (wordDerivative X I v) p volume ≤
          ENNReal.ofReal C * eLpNorm (sumSquaresWithDrift X v) p volume)
    (hdensity : ∀ v, memSobolevX driftWeight X ⊤ 2 p v →
      Nonempty (SobolevWordApproximation driftWeight X p v))
    (Ω U : Opens (Fin n → ℝ)) (u : (Fin n → ℝ) → ℝ)
    (hu : memSobolevX driftWeight X Ω 2 p u)
    (D : WeakDriftOperatorData X Ω p u) (φ : TestFunction Ω ℝ (⊤ : ℕ∞))
    (hplateau : EqOn φ 1 (U : Set (Fin n → ℝ))) (A B : ℝ≥0∞)
    (hφ : eLpNorm φ ⊤ (volume.restrict (Ω : Set (Fin n → ℝ))) ≤ 1)
    (hA : ∀ i : Fin q, eLpNorm (fieldDerivative (X i.succ) φ) ⊤
      (volume.restrict (Ω : Set (Fin n → ℝ))) ≤ A)
    (hB : eLpNorm (sumSquaresWithDrift X φ) ⊤
      (volume.restrict (Ω : Set (Fin n → ℝ))) ≤ B) :
    ∀ I : List (Fin (q+1)), wordWeight driftWeight I = 2 →
      weakWordENorm X U I p u ≤ ENNReal.ofReal C *
        (eLpNorm D.operator p (volume.restrict (Ω : Set (Fin n → ℝ))) +
          B * eLpNorm u p (volume.restrict (Ω : Set (Fin n → ℝ))) +
          2 * A * ∑ i : Fin q, weakWordENorm X Ω [i.succ] p u) := by
  exact local_second_word_of_global_estimate X hX p hp C
    (fun v hv E => second_orders_for_operator_of_compact_and_density
      X hX p hp C hcompact hdensity v hv E)
    Ω U u hu D φ hplateau A B hφ hA hB

end RothschildStein.H3
