-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.WeakDriftOperatorData
public import RothschildStein.Definitions.sumSquaresWithDrift
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open MeasureTheory TopologicalSpace
open scoped ENNReal BigOperators

/-- The weak drift product rule has a norm bound with the exact
factor two in its horizontal cross term (BB (8.62), p. 375). -/
theorem drift_cutoff_expression_norm_le {n q : ℕ}
    (X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (Ω : Opens (Fin n → ℝ)) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (u φ : (Fin n → ℝ) → ℝ) (D : WeakDriftOperatorData X Ω p u) :
    eLpNorm (fun x => D.operator x * φ x + u x * sumSquaresWithDrift X φ x +
      2 * ∑ i : Fin q, D.first i.succ x * fieldDerivative (X i.succ) φ x)
      p (volume.restrict (Ω : Set (Fin n → ℝ))) ≤
    eLpNorm φ ⊤ (volume.restrict (Ω : Set (Fin n → ℝ))) *
      eLpNorm D.operator p (volume.restrict (Ω : Set (Fin n → ℝ))) +
    eLpNorm (sumSquaresWithDrift X φ) ⊤ (volume.restrict (Ω : Set (Fin n → ℝ))) *
      eLpNorm u p (volume.restrict (Ω : Set (Fin n → ℝ))) +
    2 * ∑ i : Fin q, eLpNorm (fieldDerivative (X i.succ) φ) ⊤
      (volume.restrict (Ω : Set (Fin n → ℝ))) *
        eLpNorm (D.first i.succ) p (volume.restrict (Ω : Set (Fin n → ℝ))) := by
  let μ := volume.restrict (Ω : Set (Fin n → ℝ))
  have hmul (a b : (Fin n → ℝ) → ℝ) :
      eLpNorm (fun x => b x * a x) p μ ≤ eLpNorm a ⊤ μ * eLpNorm b p μ := by
    simpa only [Pi.smul_apply, smul_eq_mul, Pi.mul_def, mul_comm] using
      (eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm_of_pos p
        (lt_of_lt_of_le (by simp) hp) (φ := a) (f := b) (μ := μ))
  have hs : eLpNorm (fun x => ∑ i : Fin q,
      D.first i.succ x * fieldDerivative (X i.succ) φ x) p μ ≤
      ∑ i : Fin q, eLpNorm (fieldDerivative (X i.succ) φ) ⊤ μ *
        eLpNorm (D.first i.succ) p μ := by
    have hb := (eLpNorm_sum_le hp).trans
      (Finset.sum_le_sum (s := Finset.univ) (fun (i : Fin q) _ => hmul (fieldDerivative (X i.succ) φ) (D.first i.succ)))
    have he : (fun x => ∑ i : Fin q,
        D.first i.succ x * fieldDerivative (X i.succ) φ x) =
        ∑ i : Fin q, (fun x => D.first i.succ x * fieldDerivative (X i.succ) φ x) := by
      funext x
      simp only [Finset.sum_apply]
    rw [he]
    exact hb
  have ht : eLpNorm (fun x => 2 * ∑ i : Fin q,
      D.first i.succ x * fieldDerivative (X i.succ) φ x) p μ ≤
      2 * ∑ i : Fin q, eLpNorm (fieldDerivative (X i.succ) φ) ⊤ μ *
        eLpNorm (D.first i.succ) p μ := by
    have he : (fun x => 2 * ∑ i : Fin q,
        D.first i.succ x * fieldDerivative (X i.succ) φ x) =
        (2 : ℝ) • (fun x => ∑ i : Fin q,
          D.first i.succ x * fieldDerivative (X i.succ) φ x) := rfl
    rw [he, eLpNorm_const_smul]
    simpa [Real.enorm_eq_ofReal_abs] using mul_le_mul' (le_refl ‖(2 : ℝ)‖ₑ) hs
  exact (eLpNorm_add_le hp).trans (add_le_add
    ((eLpNorm_add_le hp).trans (add_le_add (hmul φ D.operator)
      (hmul (sumSquaresWithDrift X φ) u))) ht)

end RothschildStein.H3
