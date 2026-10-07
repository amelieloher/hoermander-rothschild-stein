-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.DriftCutoffBounds
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import RothschildStein.S.ClassicalWords

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open MeasureTheory TopologicalSpace Set
open scoped ENNReal BigOperators

/-- The cutoff drift expression is supported in the cutoff
domain, so its global and local Lp norms agree, including p infinity. -/
theorem driftCutoffExpression_global_norm_eq_local {n q : ℕ}
    (X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (Ω : Opens (Fin n → ℝ)) (p : ℝ≥0∞)
    (u : (Fin n → ℝ) → ℝ) (D : WeakDriftOperatorData X Ω p u)
    (φ : TestFunction Ω ℝ (⊤ : ℕ∞)) :
    eLpNorm (driftCutoffExpression D φ) p volume =
      eLpNorm (driftCutoffExpression D φ) p (volume.restrict (Ω : Set (Fin n → ℝ))) := by
  have hz : ∀ x ∉ (Ω : Set (Fin n → ℝ)), driftCutoffExpression D φ x = 0 := by
    intro x hx
    have hφ := φ.zero_on_compl hx
    have hd (V : (Fin n → ℝ) → (Fin n → ℝ)) : fieldDerivative V φ x = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      exact fun ht => hx (φ.tsupport_subset (S.tsupport_fieldDerivative_subset V φ ht))
    have hdd (V : (Fin n → ℝ) → (Fin n → ℝ)) :
        fieldDerivative V (fieldDerivative V φ) x = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      exact fun ht => hx (φ.tsupport_subset
        (S.tsupport_fieldDerivative_subset V φ
          (S.tsupport_fieldDerivative_subset V (fieldDerivative V φ) ht)))
    simp only [driftCutoffExpression, sumSquaresWithDrift, hφ, hd, hdd,
      Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
  have he : (Ω : Set (Fin n → ℝ)).indicator (driftCutoffExpression D φ) =
      driftCutoffExpression D φ := by
    funext x
    by_cases hx : x ∈ (Ω : Set (Fin n → ℝ))
    · simp only [indicator_of_mem hx]
    · simp only [indicator_of_notMem hx, hz x hx]
  calc
    eLpNorm (driftCutoffExpression D φ) p volume =
        eLpNorm ((Ω : Set (Fin n → ℝ)).indicator (driftCutoffExpression D φ)) p volume :=
      congrArg (fun f => eLpNorm f p volume) he.symm
    _ = _ := eLpNorm_indicator_eq_eLpNorm_restrict Ω.isOpen.measurableSet

/-- The global cutoff operator expression is bounded entirely
by local weak input norms and the cutoff coefficients. -/
theorem driftCutoffExpression_global_norm_le_of_bounds {n q : ℕ}
    (X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (Ω : Opens (Fin n → ℝ)) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (u : (Fin n → ℝ) → ℝ) (D : WeakDriftOperatorData X Ω p u)
    (φ : TestFunction Ω ℝ (⊤ : ℕ∞)) (A B : ℝ≥0∞)
    (hφ : eLpNorm φ ⊤ (volume.restrict (Ω : Set (Fin n → ℝ))) ≤ 1)
    (hA : ∀ i : Fin q, eLpNorm (fieldDerivative (X i.succ) φ) ⊤
      (volume.restrict (Ω : Set (Fin n → ℝ))) ≤ A)
    (hB : eLpNorm (sumSquaresWithDrift X φ) ⊤
      (volume.restrict (Ω : Set (Fin n → ℝ))) ≤ B) :
    eLpNorm (driftCutoffExpression D φ) p volume ≤
      eLpNorm D.operator p (volume.restrict (Ω : Set (Fin n → ℝ))) +
        B * eLpNorm u p (volume.restrict (Ω : Set (Fin n → ℝ))) +
        2 * A * ∑ i : Fin q, weakWordENorm X Ω [i.succ] p u := by
  rw [driftCutoffExpression_global_norm_eq_local X Ω p u D φ]
  exact driftCutoffExpression_norm_le_of_bounds X Ω p hp u φ D A B hφ hA hB

end RothschildStein.H3
