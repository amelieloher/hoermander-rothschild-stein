-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.KernelWeights

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

/-- The second-variable difference uses smoothness of the
transposed kernel, with the separation radius 4r (BB p. 320). -/
theorem KernelClass.transpose_difference_bound {μ : Measure X} {E : Set X}
    {β A S : ℝ} {K : X → X → ℝ}
    (hKt : KernelClass μ E β 0 A S (fun x y => K y x))
    {z x y : X} (hz : z ∈ E) (hx : x ∈ E) (hy : y ∈ E)
    {r : ℝ} (hr : 0 < r) (hxr : dist z x < r) (hyr : 4 * r ≤ dist z y) :
    |K y x - K y z| ≤ S * kernelWeight μ 0 z y * (r / dist z y) ^ β := by
  have hd : 0 < dist z y := by linarith
  have hsep : 2 * dist z x < dist z y := by linarith
  rw [abs_sub_comm]
  exact (hKt.smooth z hz x hx y hy hsep).trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (div_nonneg dist_nonneg hd.le)
        (div_le_div_of_nonneg_right hxr.le hd.le) hKt.β_pos.le)
      (mul_nonneg hKt.S_nonneg (kernelWeight_nonneg μ 0 z y)))

omit [MeasurableSpace X] in
/-- A nonzero kernel difference is confined to a 3κ annulus
when the kernel is supported on a ball of radius R < κ (BB p. 320). -/
theorem kernel_difference_distance_bound {K : X → X → ℝ} {xbar z x y : X}
    {R κ r : ℝ} (hR : R < κ) (hr : r ≤ κ / 5)
    (hxr : dist z x < r)
    (hsupport : ∀ a b, a ∉ ball xbar R ∨ b ∉ ball xbar R → K a b = 0)
    (hne : K y x - K y z ≠ 0) : dist z y < 3 * κ := by
  have hκ : 0 < κ := by have := dist_nonneg (x := z) (y := x); linarith
  have hy : y ∈ ball xbar R := by
    by_contra hn
    exact hne (by rw [hsupport y x (Or.inl hn), hsupport y z (Or.inl hn)]; ring)
  have hxy : x ∈ ball xbar R ∨ z ∈ ball xbar R := by
    by_contra hn
    push Not at hn
    exact hne (by rw [hsupport y x (Or.inr hn.1), hsupport y z (Or.inr hn.2)]; ring)
  have hyR : dist xbar y < R := by simpa only [mem_ball, dist_comm] using hy
  rcases hxy with hx | hz
  · have hxR : dist xbar x < R := by simpa only [mem_ball, dist_comm] using hx
    have hdist := dist_triangle z x y
    have hxy := dist_triangle x xbar y
    rw [dist_comm x xbar] at hxy
    linarith
  · have hzR : dist xbar z < R := by simpa only [mem_ball, dist_comm] using hz
    have hdist := dist_triangle z xbar y
    rw [dist_comm z xbar] at hdist
    linarith

end RothschildStein.H2
