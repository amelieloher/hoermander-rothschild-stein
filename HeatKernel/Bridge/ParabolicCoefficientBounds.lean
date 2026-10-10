-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.MatrixCoefficientBounds
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-! # Entry bounds for measurable elliptic parabolic coefficients -/

@[expose] public section
open Set MeasureTheory
namespace HeatKernel

/-- Literal symmetric quadratic bounds imply entrywise bounds on every restricted
space-time measure. The order of the two vector factors matches the scalar equation. -/
theorem ae_norm_parabolic_coefficient_entry_le {N q : ℕ}
    (a : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ)
    {lower upper : ℝ} (hlower : 0 ≤ lower)
    (hbound : ∀ᵐ z : ℝ × (Fin N → ℝ) ∂volume,
      (∀ i j, a z.1 z.2 i j = a z.1 z.2 j i) ∧
      ∀ ξ : Fin q → ℝ,
        lower * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a z.1 z.2 i j * ξ i * ξ j ∧
        ∑ i, ∑ j, a z.1 z.2 i j * ξ i * ξ j ≤ upper * ∑ i, ξ i ^ 2)
    (S : Set (ℝ × (Fin N → ℝ))) (i j : Fin q) :
    ∀ᵐ z : ℝ × (Fin N → ℝ) ∂(volume.restrict S), ‖a z.1 z.2 i j‖ ≤ upper := by
  filter_upwards [ae_restrict_of_ae hbound] with z hz
  apply norm_matrix_entry_le_of_elliptic_bounds (fun i j => a z.1 z.2 i j) hlower hz.1 _ i j
  intro ξ
  have he : matrixEnergy (fun i j => a z.1 z.2 i j) ξ =
      ∑ i, ∑ j, a z.1 z.2 i j * ξ i * ξ j := by
    unfold matrixEnergy
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simpa only [he, coordinateNormSq] using hz.2 ξ

end HeatKernel
