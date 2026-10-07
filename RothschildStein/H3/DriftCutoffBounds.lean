-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.DriftCutoffNorm
public import RothschildStein.S.DriftProduct
public import RothschildStein.S.Sobolev

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open MeasureTheory TopologicalSpace
open scoped ENNReal BigOperators

/-- The actual weak operator of a cutoff product, with its transpose
pairing, is the corrected drift Leibniz expression (BB p. 375). -/
def driftCutoffExpression {n q : ℕ}
    {X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ)}
    {Ω : Opens (Fin n → ℝ)} {p : ℝ≥0∞} {u : (Fin n → ℝ) → ℝ}
    (D : WeakDriftOperatorData X Ω p u) (φ : (Fin n → ℝ) → ℝ) :
    (Fin n → ℝ) → ℝ := fun x =>
  D.operator x * φ x + u x * sumSquaresWithDrift X φ x +
    2 * ∑ i : Fin q, D.first i.succ x * fieldDerivative (X i.succ) φ x

/-- Explicit coefficient form of the operator cutoff estimate, ready
to use with the smooth quasiball cutoff constants. -/
theorem driftCutoffExpression_norm_le_of_bounds {n q : ℕ}
    (X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (Ω : Opens (Fin n → ℝ)) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (u φ : (Fin n → ℝ) → ℝ) (D : WeakDriftOperatorData X Ω p u)
    (A B : ℝ≥0∞)
    (hφ : eLpNorm φ ⊤ (volume.restrict (Ω : Set (Fin n → ℝ))) ≤ 1)
    (hA : ∀ i : Fin q, eLpNorm (fieldDerivative (X i.succ) φ) ⊤
      (volume.restrict (Ω : Set (Fin n → ℝ))) ≤ A)
    (hB : eLpNorm (sumSquaresWithDrift X φ) ⊤
      (volume.restrict (Ω : Set (Fin n → ℝ))) ≤ B) :
    eLpNorm (driftCutoffExpression D φ) p (volume.restrict (Ω : Set (Fin n → ℝ))) ≤
      eLpNorm D.operator p (volume.restrict (Ω : Set (Fin n → ℝ))) +
        B * eLpNorm u p (volume.restrict (Ω : Set (Fin n → ℝ))) +
        2 * A * ∑ i : Fin q, weakWordENorm X Ω [i.succ] p u := by
  have hb := drift_cutoff_expression_norm_le X Ω p hp u φ D
  have hs : (∑ i : Fin q, eLpNorm (fieldDerivative (X i.succ) φ) ⊤
      (volume.restrict (Ω : Set (Fin n → ℝ))) *
        eLpNorm (D.first i.succ) p (volume.restrict (Ω : Set (Fin n → ℝ)))) ≤
      A * ∑ i : Fin q, weakWordENorm X Ω [i.succ] p u := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [S.weakWordENorm_eq X Ω [i.succ] p u _ (D.first_weak i.succ)]
    exact mul_le_mul' (hA i) (le_refl _)
  have hfirst : eLpNorm φ ⊤ (volume.restrict (Ω : Set (Fin n → ℝ))) *
      eLpNorm D.operator p (volume.restrict (Ω : Set (Fin n → ℝ))) ≤
      eLpNorm D.operator p (volume.restrict (Ω : Set (Fin n → ℝ))) := by
    simpa only [one_mul] using mul_le_mul' hφ (le_refl
      (eLpNorm D.operator p (volume.restrict (Ω : Set (Fin n → ℝ)))))
  exact hb.trans (by
    simpa only [mul_assoc] using add_le_add
      (add_le_add hfirst (mul_le_mul' hB (le_refl _)))
      (mul_le_mul' (le_refl (2 : ℝ≥0∞)) hs))

end RothschildStein.H3
