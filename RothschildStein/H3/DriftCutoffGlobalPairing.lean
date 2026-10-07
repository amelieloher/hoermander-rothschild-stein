-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.CutoffWeakWordExtension
public import RothschildStein.H3.DriftCutoffBounds
public import RothschildStein.H3.WeakOperatorPairing

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory TopologicalSpace
open scoped BigOperators ENNReal

/-- Zero extension of the corrected local drift expression is
the actual global weak operator of an interior cutoff product. -/
theorem driftCutoffExpression_zeroExtension_pairing {n q : ℕ}
    (X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (Ω : Opens (Fin n → ℝ)) (p : ℝ≥0∞)
    (u : (Fin n → ℝ) → ℝ) (D : WeakDriftOperatorData X Ω p u)
    (φ : TestFunction Ω ℝ (⊤ : ℕ∞))
    (ψ : TestFunction (⊤ : Opens (Fin n → ℝ)) ℝ (⊤ : ℕ∞)) :
    (∫ x, (Ω : Set (Fin n → ℝ)).indicator (driftCutoffExpression D φ) x * ψ x) =
      ∫ x, u x * φ x * sumSquaresWithDriftTranspose X ψ x := by
  let P : Fin (q+1) → (Fin n → ℝ) → ℝ := fun i x =>
    D.first i x * φ x + u x * fieldDerivative (X i) φ x
  let Q : Fin q → (Fin n → ℝ) → ℝ := fun i x =>
    D.square i x * φ x + 2 * D.first i.succ x * fieldDerivative (X i.succ) φ x +
      u x * fieldDerivative (X i.succ) (fieldDerivative (X i.succ) φ) x
  let g := fun i => (Ω : Set (Fin n → ℝ)).indicator (P i)
  let h := fun i => (Ω : Set (Fin n → ℝ)).indicator (Q i)
  have hg : ∀ i, hasWeakWordDeriv X ⊤ [i] (fun x => u x * φ x) (g i) := by
    intro i
    exact cutoff_weak_word_extension X Ω [i] u (P i) φ
      (S.hasWeakWordDeriv_mul_one X Ω (fun j => (hX j).contDiffOn) i u
        (D.first i) φ φ.contDiff.contDiffOn (D.first_weak i))
  have hh : ∀ i : Fin q, hasWeakWordDeriv X ⊤ [i.succ,i.succ]
      (fun x => u x * φ x) (h i) := by
    intro i
    exact cutoff_weak_word_extension X Ω [i.succ,i.succ] u (Q i) φ
      (S.hasWeakWordDeriv_mul_square X Ω (fun j => (hX j).contDiffOn) i.succ u
        (D.first i.succ) (D.square i) φ φ.contDiff.contDiffOn
        (D.first_weak i.succ) (D.square_weak i))
  have he : (fun x => g 0 x + ∑ i, h i x) =
      (Ω : Set (Fin n → ℝ)).indicator (driftCutoffExpression D φ) := by
    funext x
    by_cases hx : x ∈ (Ω : Set (Fin n → ℝ))
    · simp only [g, h, indicator_of_mem hx, P, Q, driftCutoffExpression,
        WeakDriftOperatorData.operator, sumSquaresWithDrift,
        Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum, mul_add, add_mul]
      simp only [mul_assoc]
      ring
    · simp only [g, h, indicator_of_notMem hx, Finset.sum_const_zero, add_zero]
  have hb := integral_sumSquaresWithDrift_weak_jets X ⊤ (fun i => (hX i).contDiffOn)
    (fun x => u x * φ x) g h hg hh ψ
  simp only [Opens.coe_top, Measure.restrict_univ] at hb
  change (∫ x, (fun y => g 0 y + ∑ i, h i y) x * ψ x) = _ at hb
  rw [he] at hb
  exact hb

end RothschildStein.H3
