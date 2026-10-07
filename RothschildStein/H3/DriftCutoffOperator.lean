-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.DriftCutoffLp
public import RothschildStein.H3.DriftCutoffGlobalPairing
public import RothschildStein.H3.WeakDriftOperatorUniqueness
public import RothschildStein.H3.CutoffSobolevGlobal

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open MeasureTheory TopologicalSpace
open scoped ENNReal BigOperators

/-- The actual global Sobolev operator of an interior cutoff
product equals the zero-extended corrected local Leibniz expression. -/
theorem exists_cutoff_weakDriftOperatorData {n q : ℕ}
    (X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (Ω : Opens (Fin n → ℝ)) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (u : (Fin n → ℝ) → ℝ) (hu : memSobolevX driftWeight X Ω 2 p u)
    (D : WeakDriftOperatorData X Ω p u) (φ : TestFunction Ω ℝ (⊤ : ℕ∞)) :
    ∃ E : WeakDriftOperatorData X ⊤ p (fun x => u x * φ x),
      E.operator =ᵐ[volume] (Ω : Set (Fin n → ℝ)).indicator (driftCutoffExpression D φ) := by
  have hglobal := cutoff_memSobolevX_global driftWeight X Ω
    (fun i => (hX i).contDiffOn) 2 p hp u hu φ
  obtain ⟨E⟩ := exists_weakDriftOperatorData X ⊤ p (fun x => u x * φ x) hglobal
  have hF := driftCutoffExpression_zeroExtension_memLp X hX Ω p u hu.1 D φ
  refine ⟨E, ?_⟩
  have he := E.operator_ae_eq_of_pairing (fun i => (hX i).contDiffOn) hp
    (by simpa only [Opens.coe_top, Measure.restrict_univ] using hF)
    (fun ψ => by simpa only [Opens.coe_top, Measure.restrict_univ] using
      driftCutoffExpression_zeroExtension_pairing X hX Ω p u D φ ψ)
  simpa only [Opens.coe_top, Measure.restrict_univ] using he

/-- The global weighted second-order operator norm is bounded by the
local input operator and horizontal jets. -/
theorem exists_cutoff_operator_norm_le_of_bounds {n q : ℕ}
    (X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (Ω : Opens (Fin n → ℝ)) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (u : (Fin n → ℝ) → ℝ) (hu : memSobolevX driftWeight X Ω 2 p u)
    (D : WeakDriftOperatorData X Ω p u) (φ : TestFunction Ω ℝ (⊤ : ℕ∞))
    (A B : ℝ≥0∞)
    (hφ : eLpNorm φ ⊤ (volume.restrict (Ω : Set (Fin n → ℝ))) ≤ 1)
    (hA : ∀ i : Fin q, eLpNorm (fieldDerivative (X i.succ) φ) ⊤
      (volume.restrict (Ω : Set (Fin n → ℝ))) ≤ A)
    (hB : eLpNorm (sumSquaresWithDrift X φ) ⊤
      (volume.restrict (Ω : Set (Fin n → ℝ))) ≤ B) :
    ∃ E : WeakDriftOperatorData X ⊤ p (fun x => u x * φ x),
      eLpNorm E.operator p volume ≤
        eLpNorm D.operator p (volume.restrict (Ω : Set (Fin n → ℝ))) +
          B * eLpNorm u p (volume.restrict (Ω : Set (Fin n → ℝ))) +
          2 * A * ∑ i : Fin q, weakWordENorm X Ω [i.succ] p u := by
  obtain ⟨E, he⟩ := exists_cutoff_weakDriftOperatorData X hX Ω p hp u hu D φ
  refine ⟨E, ?_⟩
  rw [eLpNorm_congr_ae he, eLpNorm_indicator_eq_eLpNorm_restrict Ω.isOpen.measurableSet]
  exact driftCutoffExpression_norm_le_of_bounds X Ω p hp u φ D A B hφ hA hB

end RothschildStein.H3
