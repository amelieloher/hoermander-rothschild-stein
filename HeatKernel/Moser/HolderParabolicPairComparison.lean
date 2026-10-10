-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.ParabolicMetric
public import HeatKernel.Moser.HolderPairComparison
public import HeatKernel.Moser.HolderFarPairs
import Mathlib.Tactic

/-! # Parabolic pair bounds from rational-cylinder oscillations -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
namespace HeatKernel

/-- Rational-cylinder decay and a global oscillation bound control all pairs in
an interior cylinder, including pairs separated by a fixed fraction of its radius. -/
theorem abs_sub_le_of_parabolic_rational_cylinder_oscillation
    {X : Type*} [MetricSpace X] (c : ℕ → X) (hc : DenseRange c)
    (u : ℝ × X → ℝ) (ω : ℝ → X → ℝ → ℝ)
    (z w : ParabolicSpaceTime X) {x₀ : X} {top r a θ W : ℝ}
    (hr : 0 < r) (hzx : dist z.2 x₀ < r) (hzt : top - r ^ 2 < z.1.val)
    (htop : max z.1.val w.1.val < top)
    (ha : 0 ≤ a) (hθ : 0 ≤ θ) (hθa : θ ≤ (1 / 2 : ℝ) ^ a) (hW : 0 ≤ W)
    (hglobal : |u (z.1.val, z.2) - u (w.1.val, w.2)| ≤ W)
    (hpair : ∀ (τ ρ : ℚ) (i : ℕ),
      (z.1.val, z.2) ∈ Ioo ((τ : ℝ) - (ρ : ℝ) ^ 2) τ ×ˢ ball (c i) ρ →
      (w.1.val, w.2) ∈ Ioo ((τ : ℝ) - (ρ : ℝ) ^ 2) τ ×ˢ ball (c i) ρ →
      |u (z.1.val, z.2) - u (w.1.val, w.2)| ≤ ω τ (c i) ρ)
    (hmono : ∀ τ i, MonotoneOn (ω τ (c i)) (Icc 0 (15 * r / 32)))
    (hdecay : ∀ τ i,
      Ioo (τ - 4 * (15 * r / 32) ^ 2) τ ×ˢ ball (c i) (2 * (15 * r / 32)) ⊆
        Ioo (top - 4 * r ^ 2) top ×ˢ ball x₀ (2 * r) →
      ∀ n : ℕ, ω τ (c i) ((15 * r / 32) * (1 / 2 : ℝ) ^ n) ≤ θ ^ n * W) :
    |u (z.1.val, z.2) - u (w.1.val, w.2)| ≤
      (1024 / 15 : ℝ) ^ a * (dist z w / r) ^ a * W := by
  by_cases heq : z = w
  · subst w
    simp only [sub_self, abs_zero]
    positivity
  have hδ : 0 < dist z w := dist_pos.mpr heq
  by_cases hnear : dist z w < r / 64
  · have hsqrt : Real.sqrt |z.1.val - w.1.val| ≤ dist z w := by
      rw [parabolicSpaceTime_dist]
      exact le_max_left _ _
    have htime : |z.1.val - w.1.val| ≤ dist z w ^ 2 := by
      nlinarith [Real.sq_sqrt (abs_nonneg (z.1.val - w.1.val)),
        Real.sqrt_nonneg |z.1.val - w.1.val|]
    have hspace : dist z.2 w.2 ≤ dist z w := by
      rw [parabolicSpaceTime_dist]
      exact le_max_right _ _
    exact abs_sub_le_of_rational_cylinder_oscillation c hc u ω hr hδ hnear
      hzx hzt htop htime hspace ha hθ hθa hW hpair hmono hdecay
  · have hfar := abs_sub_le_holder_of_separation hr ha hW (le_of_not_gt hnear) hglobal
    have hconstant : (64 : ℝ) ^ a ≤ (1024 / 15 : ℝ) ^ a :=
      Real.rpow_le_rpow (by norm_num) (by norm_num) ha
    exact hfar.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hconstant (Real.rpow_nonneg (by positivity) _)) hW)

end HeatKernel
