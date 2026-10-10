-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Semigroup.HorizontalEulerApproximation
public import HeatKernel.Semigroup.ScaledResolventOrder
public import HeatKernel.Semigroup.L2OrderLimits

/-! # Order bounds for the horizontal heat operators

The scaled form resolvents preserve the order interval from zero to one. Their Euler
approximants converge in L², and subsequence convergence preserves both bounds.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped NNReal
namespace HeatKernel
variable {N q : ℕ} (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))

theorem scaledHorizontalFormResolvent_pow_nonneg
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (scale : ℝ) (hscale : 0 < scale) (n : ℕ)
    (f : SpatialL2 (N := N) ⊤) (hf : ∀ᵐ x ∂volume, 0 ≤ f x) :
    ∀ᵐ x ∂volume, 0 ≤ (scaledHorizontalFormResolvent ⊤ X scale hscale ^ n) f x := by
  induction n with
  | zero => simpa only [pow_zero, one_apply_eq_self] using hf
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp]
    exact scaledHorizontalFormResolvent_nonneg X hX scale hscale _ ih

theorem scaledHorizontalFormResolvent_pow_le_one
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (scale : ℝ) (hscale : 0 < scale) (n : ℕ)
    (f : SpatialL2 (N := N) ⊤) (hf : ∀ᵐ x ∂volume, f x ≤ 1) :
    ∀ᵐ x ∂volume, (scaledHorizontalFormResolvent ⊤ X scale hscale ^ n) f x ≤ 1 := by
  induction n with
  | zero => simpa only [pow_zero, one_apply_eq_self] using hf
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp]
    exact scaledHorizontalFormResolvent_le_one X hX scale hscale _ ih

theorem horizontalHeatOperator_nonneg
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (t : ℝ≥0)
    (f : SpatialL2 (N := N) ⊤) (hf : ∀ᵐ x ∂volume, 0 ≤ f x) :
    ∀ᵐ x ∂volume, 0 ≤ horizontalHeatOperator ⊤ X t f x := by
  by_cases ht : t = 0
  · subst t
    simpa only [horizontalHeatOperator_zero, one_apply_eq_self] using hf
  have ht' : 0 < (t : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr ht)
  have hlim := tendsto_horizontalEulerOperator_apply ⊤ X (fun i => (hX i).contDiffOn) (t : ℝ) ht' f
  have hn (n : ℕ) : ∀ᵐ x ∂volume.restrict (⊤ : Opens (Fin N → ℝ)),
      0 ≤ horizontalEulerOperator ⊤ X (t : ℝ) ht' n f x := by
    simpa only [horizontalEulerOperator, Opens.coe_top, Measure.restrict_univ] using
      scaledHorizontalFormResolvent_pow_nonneg X hX _
        (div_pos ht' (by exact_mod_cast Nat.succ_pos n)) (n + 1) f hf
  simpa only [Real.toNNReal_coe, Opens.coe_top, Measure.restrict_univ] using
    ae_nonneg_of_tendsto_L2 hlim hn

theorem horizontalHeatOperator_le_one
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (t : ℝ≥0)
    (f : SpatialL2 (N := N) ⊤) (hf : ∀ᵐ x ∂volume, f x ≤ 1) :
    ∀ᵐ x ∂volume, horizontalHeatOperator ⊤ X t f x ≤ 1 := by
  by_cases ht : t = 0
  · subst t
    simpa only [horizontalHeatOperator_zero, one_apply_eq_self] using hf
  have ht' : 0 < (t : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr ht)
  have hlim := tendsto_horizontalEulerOperator_apply ⊤ X (fun i => (hX i).contDiffOn) (t : ℝ) ht' f
  have hn (n : ℕ) : ∀ᵐ x ∂volume.restrict (⊤ : Opens (Fin N → ℝ)),
      horizontalEulerOperator ⊤ X (t : ℝ) ht' n f x ≤ 1 := by
    simpa only [horizontalEulerOperator, Opens.coe_top, Measure.restrict_univ] using
      scaledHorizontalFormResolvent_pow_le_one X hX _
        (div_pos ht' (by exact_mod_cast Nat.succ_pos n)) (n + 1) f hf
  simpa only [Real.toNNReal_coe, Opens.coe_top, Measure.restrict_univ] using
    ae_le_const_of_tendsto_L2 hlim hn

end HeatKernel
