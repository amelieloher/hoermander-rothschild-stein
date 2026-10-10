-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Tactic.Linarith

/-! Radius and shadow estimates from a Lipschitz boundary-distance function. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace HeatKernel

/-- Overlapping dilates of balls whose radii are boundary distance divided by a common
large constant have comparable radii. -/
theorem radius_le_two_mul_of_boundaryDistance {E : Type*} [PseudoMetricSpace E]
    {δ : E → ℝ} (hδ : LipschitzWith 1 δ) {x y : E} {a b κ c : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hκ : 3 * c < κ)
    (hx : δ x = κ * a) (hy : δ y = κ * b)
    (hxy : dist x y ≤ c * (a + b)) : a ≤ 2 * b := by
  have hd : δ x - δ y ≤ dist x y := by
    have hh := hδ.dist_le_mul x y
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using
      (le_abs_self (δ x - δ y)).trans hh
  rw [hx, hy] at hd
  have hk : 0 < κ - c := by linarith
  have hab : (κ - c) * a ≤ (κ + c) * b := by nlinarith
  by_contra hn
  have hb : b < a / 2 := by linarith
  have hmul := mul_lt_mul_of_pos_left hb hk
  nlinarith [mul_nonneg hc ha]

/-- A meeting point of a path with a small ball bounds the distance from the starting
center by the radius of that ball, provided boundary distance dominates elapsed length. -/
theorem dist_start_le_of_path_meeting {E : Type*} [PseudoMetricSpace E]
    {δ : E → ℝ} (hδ : LipschitzWith 1 δ) {x z w : E} {a κ c s : ℝ}
    (hz : δ z = κ * a) (hstart : dist x w ≤ s) (hs : s ≤ δ w)
    (hmeet : dist w z ≤ c * a) : dist x z ≤ (κ + 2 * c) * a := by
  have hd : δ w ≤ δ z + dist w z := by
    have hh := hδ.dist_le_mul w z
    have hh' : δ w - δ z ≤ dist w z := by
      simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using
        (le_abs_self (δ w - δ z)).trans hh
    linarith
  have ht := dist_triangle x w z
  rw [hz] at hd
  nlinarith

/-- A lower bound for boundary distance along a path gives a lower bound for the radius
of every ball whose small dilate meets the path. -/
theorem radius_third_le_of_path_meeting {E : Type*} [PseudoMetricSpace E]
    {δ : E → ℝ} (hδ : LipschitzWith 1 δ) {z w : E} {a b κ c : ℝ}
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hκ : 2 * c ≤ κ) (hkpos : 0 < κ)
    (hz : δ z = κ * a) (hboundary : κ * b / 2 ≤ δ w)
    (hmeet : dist w z ≤ c * a) : b / 3 ≤ a := by
  have hh := hδ.dist_le_mul w z
  have hd : δ w - δ z ≤ dist w z := by
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using
      (le_abs_self (δ w - δ z)).trans hh
  rw [hz] at hd
  have hapos : 0 ≤ a := by
    by_contra hn
    have : (κ + c) * a < 0 := mul_neg_of_pos_of_neg (by linarith) (by linarith)
    nlinarith [mul_nonneg hkpos.le hb]
  have hca := mul_nonneg hapos (sub_nonneg.mpr hκ)
  nlinarith

end HeatKernel
