-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.WeightedChainSummation

/-! Converting weighted chain power estimates to unnormalized local energy sums. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped NNReal ENNReal BigOperators Classical

namespace HeatKernel

/-- Normalized vertex costs, a radius bound, and the shadow estimate convert weighted
chain powers into an unnormalized sum of local energies. -/
theorem tsum_mul_chain_rpow_le_energy_sum {ι κ : Type*}
    (chain : ι → Finset κ) (m : ι → ℝ≥0∞) (v g : κ → ℝ≥0∞)
    (w h : κ → ℝ≥0) {p : ℝ} (hp : 1 ≤ p) (R r : ℝ≥0) (H : ℝ≥0∞)
    (hradius : ∀ i, ∑ j ∈ chain i, w j ≤ R)
    (hmax : ∀ j, w j ≤ r)
    (hshadow : ∀ j, (∑' i : {i | j ∈ chain i}, m i.val) ≤ H * v j)
    (henergy : ∀ j, v j * ((h j ^ p : ℝ≥0) : ℝ≥0∞) ≤ g j) :
    (∑' i, m i * (((∑ j ∈ chain i, w j * h j) ^ p : ℝ≥0) : ℝ≥0∞)) ≤
      ((R ^ (p - 1) : ℝ≥0) : ℝ≥0∞) * H * r * ∑' j, g j := by
  have hc : ∀ j, v j * ((w j * h j ^ p : ℝ≥0) : ℝ≥0∞) ≤ (r : ℝ≥0∞) * g j := by
    intro j
    calc
      v j * ((w j * h j ^ p : ℝ≥0) : ℝ≥0∞) =
          (w j : ℝ≥0∞) * (v j * ((h j ^ p : ℝ≥0) : ℝ≥0∞)) := by
        rw [ENNReal.coe_mul]
        ac_rfl
      _ ≤ (w j : ℝ≥0∞) * g j := mul_le_mul_right (henergy j) (w j : ℝ≥0∞)
      _ ≤ (r : ℝ≥0∞) * g j := mul_le_mul_left (ENNReal.coe_le_coe.mpr (hmax j)) (g j)
  have hs : (∑' j, v j * ((w j * h j ^ p : ℝ≥0) : ℝ≥0∞)) ≤ r * ∑' j, g j := by
    rw [← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum hc
  calc
    (∑' i, m i * (((∑ j ∈ chain i, w j * h j) ^ p : ℝ≥0) : ℝ≥0∞)) ≤
        ((R ^ (p - 1) : ℝ≥0) : ℝ≥0∞) * H *
          ∑' j, v j * ((w j * h j ^ p : ℝ≥0) : ℝ≥0∞) :=
      tsum_mul_chain_rpow_le_of_shadow_bound chain m v w h hp R H hradius hshadow
    _ ≤ ((R ^ (p - 1) : ℝ≥0) : ℝ≥0∞) * H * (r * ∑' j, g j) :=
      mul_le_mul_right hs _
    _ = ((R ^ (p - 1) : ℝ≥0) : ℝ≥0∞) * H * r * ∑' j, g j := (mul_assoc _ _ _).symm

end HeatKernel
