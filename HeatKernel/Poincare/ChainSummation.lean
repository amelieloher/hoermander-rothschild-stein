-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! Rearrangement of nonnegative chain sums through their shadows. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped ENNReal BigOperators Classical

namespace HeatKernel

/-- Interchanging nonnegative chain sums groups the starting weights by the shadow of
each chain vertex. No preliminary finiteness of either sum is required. -/
theorem tsum_mul_chain_sum_eq_tsum_shadow_mul {ι κ : Type*}
    (chain : ι → Finset κ) (m : ι → ℝ≥0∞) (c : κ → ℝ≥0∞) :
    (∑' i, m i * ∑ j ∈ chain i, c j) =
      ∑' j, (∑' i : {i | j ∈ chain i}, m i.val) * c j := by
  calc
    (∑' i, m i * ∑ j ∈ chain i, c j) =
        ∑' i, ∑' j, if j ∈ chain i then m i * c j else 0 := by
      congr 1
      funext i
      rw [sum_eq_tsum_indicator, ← ENNReal.tsum_mul_left]
      congr 1
      funext j
      by_cases hj : j ∈ chain i <;> simp [hj]
    _ = ∑' j, ∑' i, if j ∈ chain i then m i * c j else 0 := ENNReal.tsum_comm
    _ = ∑' j, (∑' i : {i | j ∈ chain i}, m i.val) * c j := by
      congr 1
      funext j
      rw [tsum_subtype, ← ENNReal.tsum_mul_right]
      congr 1
      funext i
      by_cases hj : j ∈ chain i <;> simp [hj]

/-- A shadow bound turns the nonnegative chain sum into the corresponding vertex sum. -/
theorem tsum_mul_chain_sum_le_of_shadow_bound {ι κ : Type*}
    (chain : ι → Finset κ) (m : ι → ℝ≥0∞) (c v : κ → ℝ≥0∞) (H : ℝ≥0∞)
    (hshadow : ∀ j, (∑' i : {i | j ∈ chain i}, m i.val) ≤ H * v j) :
    (∑' i, m i * ∑ j ∈ chain i, c j) ≤ H * ∑' j, v j * c j := by
  rw [tsum_mul_chain_sum_eq_tsum_shadow_mul, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro j
  simpa only [mul_assoc] using mul_le_mul_left (hshadow j) (c j)

end HeatKernel
