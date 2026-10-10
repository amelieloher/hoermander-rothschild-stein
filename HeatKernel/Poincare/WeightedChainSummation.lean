-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.ChainSummation
public import HeatKernel.Poincare.WeightedHolder

/-! Weighted Hölder and shadow bounds for nonnegative chain power sums. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped NNReal ENNReal BigOperators Classical

namespace HeatKernel

/-- A uniform radius sum and a shadow bound control weighted chain powers, including
exponent one, before any finiteness conclusion is known. -/
theorem tsum_mul_chain_rpow_le_of_shadow_bound {ι κ : Type*}
    (chain : ι → Finset κ) (m : ι → ℝ≥0∞) (v : κ → ℝ≥0∞)
    (w h : κ → ℝ≥0) {p : ℝ} (hp : 1 ≤ p) (R : ℝ≥0) (H : ℝ≥0∞)
    (hradius : ∀ i, ∑ j ∈ chain i, w j ≤ R)
    (hshadow : ∀ j, (∑' i : {i | j ∈ chain i}, m i.val) ≤ H * v j) :
    (∑' i, m i * (((∑ j ∈ chain i, w j * h j) ^ p : ℝ≥0) : ℝ≥0∞)) ≤
      ((R ^ (p - 1) : ℝ≥0) : ℝ≥0∞) * H *
        ∑' j, v j * ((w j * h j ^ p : ℝ≥0) : ℝ≥0∞) := by
  let A : ℝ≥0∞ := (R ^ (p - 1) : ℝ≥0)
  let c : κ → ℝ≥0∞ := fun j => (w j * h j ^ p : ℝ≥0)
  have hholder : ∀ i, (((∑ j ∈ chain i, w j * h j) ^ p : ℝ≥0) : ℝ≥0∞) ≤
      A * ∑ j ∈ chain i, c j := by
    intro i
    have hh := ENNReal.coe_le_coe.mpr (rpow_sum_mul_le_of_sum_le (chain i) w h hp (hradius i))
    simpa only [A, c, ENNReal.coe_mul, ENNReal.ofNNReal_finsetSum] using hh
  calc
    (∑' i, m i * (((∑ j ∈ chain i, w j * h j) ^ p : ℝ≥0) : ℝ≥0∞)) ≤
        ∑' i, m i * (A * ∑ j ∈ chain i, c j) :=
      ENNReal.tsum_le_tsum fun i => mul_le_mul_right (hholder i) (m i)
    _ = A * ∑' i, m i * ∑ j ∈ chain i, c j := by
      rw [← ENNReal.tsum_mul_left]
      congr 1
      funext i
      ac_rfl
    _ ≤ A * (H * ∑' j, v j * c j) :=
      mul_le_mul_right (tsum_mul_chain_sum_le_of_shadow_bound chain m c v H hshadow) A
    _ = A * H * ∑' j, v j * c j := (mul_assoc _ _ _).symm

end HeatKernel
