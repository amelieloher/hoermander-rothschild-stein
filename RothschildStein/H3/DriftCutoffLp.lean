-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.DriftCutoffBounds
public import RothschildStein.H3.SobolevOperatorData
public import RothschildStein.H3.CompactOperatorLp
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open MeasureTheory TopologicalSpace
open scoped ENNReal BigOperators

/-- The corrected cutoff expression belongs to local Lp:
its smooth compact coefficients are actual bounded multipliers. -/
theorem driftCutoffExpression_memLp {n q : ℕ}
    (X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (Ω : Opens (Fin n → ℝ)) (p : ℝ≥0∞)
    (u : (Fin n → ℝ) → ℝ) (hu : MemLp u p (volume.restrict (Ω : Set (Fin n → ℝ))))
    (D : WeakDriftOperatorData X Ω p u) (φ : TestFunction Ω ℝ (⊤ : ℕ∞)) :
    MemLp (driftCutoffExpression D φ) p (volume.restrict (Ω : Set (Fin n → ℝ))) := by
  let μ := volume.restrict (Ω : Set (Fin n → ℝ))
  have hφ : MemLp (φ : (Fin n → ℝ) → ℝ) ⊤ μ :=
    (φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport).mono_measure
      Measure.restrict_le_self
  have hL : MemLp (sumSquaresWithDrift X φ) ⊤ μ :=
    (memLp_sumSquaresWithDrift_compact X hX φ φ.contDiff φ.hasCompactSupport ⊤).mono_measure
      Measure.restrict_le_self
  have hd : ∀ i : Fin (q+1), MemLp (fieldDerivative (X i) φ) ⊤ μ := by
    intro i
    simpa only [wordDerivative] using
      (memLp_wordDerivative_compact X hX [i] φ.contDiff φ.hasCompactSupport ⊤).mono_measure
        Measure.restrict_le_self
  have hs : MemLp (fun x => ∑ i : Fin q,
      D.first i.succ x * fieldDerivative (X i.succ) φ x) p μ :=
    memLp_finsetSum Finset.univ (fun i _ => (D.first_memLp i.succ).fun_mul (hd i.succ))
  have ht : MemLp (fun x => 2 * ∑ i : Fin q,
      D.first i.succ x * fieldDerivative (X i.succ) φ x) p μ := by
    convert hs.const_smul (2 : ℝ) using 1
  exact ((D.operator_memLp.fun_mul hφ).add (hu.fun_mul hL)).add ht

/-- The global zero extension of the cutoff expression is Lp,
without an extra operator integrability premise. -/
theorem driftCutoffExpression_zeroExtension_memLp {n q : ℕ}
    (X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (Ω : Opens (Fin n → ℝ)) (p : ℝ≥0∞)
    (u : (Fin n → ℝ) → ℝ) (hu : MemLp u p (volume.restrict (Ω : Set (Fin n → ℝ))))
    (D : WeakDriftOperatorData X Ω p u) (φ : TestFunction Ω ℝ (⊤ : ℕ∞)) :
    MemLp ((Ω : Set (Fin n → ℝ)).indicator (driftCutoffExpression D φ)) p volume :=
  (memLp_indicator_iff_restrict Ω.isOpen.measurableSet).mpr
    (driftCutoffExpression_memLp X hX Ω p u hu D φ)

end RothschildStein.H3
