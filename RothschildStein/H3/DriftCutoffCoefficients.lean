-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Definitions.sumSquaresWithDrift
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open MeasureTheory
open scoped ENNReal BigOperators

/-- The weight-two cutoff bounds give the drift-operator cutoff bound
with coefficient q + 1 (BB p. 375). -/
theorem sumSquaresWithDrift_norm_le_of_field_bounds {n q : ℕ}
    (X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (φ : (Fin n → ℝ) → ℝ) (μ : Measure (Fin n → ℝ))
    (p : ℝ≥0∞) (hp : 1 ≤ p) (B : ℝ≥0∞)
    (h₀ : eLpNorm (fieldDerivative (X 0) φ) p μ ≤ B)
    (hs : ∀ i : Fin q, eLpNorm
      (fieldDerivative (X i.succ) (fieldDerivative (X i.succ) φ)) p μ ≤ B) :
    eLpNorm (sumSquaresWithDrift X φ) p μ ≤ (q+1 : ℝ≥0∞) * B := by
  have he : sumSquaresWithDrift X φ = fieldDerivative (X 0) φ +
      (fun x => ∑ i : Fin q,
        fieldDerivative (X i.succ) (fieldDerivative (X i.succ) φ) x) := rfl
  rw [he]
  have hsum : eLpNorm (fun x => ∑ i : Fin q,
      fieldDerivative (X i.succ) (fieldDerivative (X i.succ) φ) x) p μ ≤
      (q : ℝ≥0∞) * B := by
    have hb := (eLpNorm_sum_le hp).trans
      (Finset.sum_le_sum (s := Finset.univ) (fun i _ => hs i))
    simpa only [← Finset.sum_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hb
  have hb := (eLpNorm_add_le hp).trans (add_le_add h₀ hsum)
  simpa only [add_mul, one_mul, add_comm] using hb

end RothschildStein.H3
