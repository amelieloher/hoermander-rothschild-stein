-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.SecondOrderSelectedOperator
public import RothschildStein.H3.DriftCutoffOperator
public import RothschildStein.H3.CutoffInnerNorm

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory TopologicalSpace
open scoped ENNReal BigOperators

/-- A local second word is bounded by the local operator, input, and
first words under the global second-word estimate. -/
theorem local_second_word_of_global_estimate {n q : ℕ}
    (X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (p : ℝ≥0∞) (hp : 1 ≤ p) (C : ℝ)
    (hglobal : ∀ v, memSobolevX driftWeight X ⊤ 2 p v →
      ∀ E : WeakDriftOperatorData X ⊤ p v,
      ∀ I : List (Fin (q+1)), wordWeight driftWeight I = 2 →
        weakWordENorm X ⊤ I p v ≤ ENNReal.ofReal C * eLpNorm E.operator p volume)
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
  have hs := cutoff_memSobolevX_global driftWeight X Ω
    (fun i => (hX i).contDiffOn) 2 p hp u hu φ
  obtain ⟨E, hE⟩ := exists_cutoff_operator_norm_le_of_bounds X hX Ω p hp u hu
    D φ A B hφ hA hB
  intro I hI
  have hi : I ∈ wordFamily driftWeight 2 := by simp [S.mem_wordFamily_iff, hI]
  obtain ⟨g, hg, _⟩ := hs.2 I hi
  have hinner := cutoff_plateau_weakNorm_le X U I p u φ g hplateau hg
  exact hinner.trans ((hglobal _ hs E I hI).trans (mul_le_mul' (le_refl _) hE))

end RothschildStein.H3
