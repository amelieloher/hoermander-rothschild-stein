-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.MetricSegment
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-! Boundary-distance lower bounds along segments toward the center of a metric ball. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric

namespace HeatKernel

/-- The distance to the complement of a ball is at least the radius minus the distance
to its center. -/
theorem sub_dist_le_infDist_compl_ball {E : Type*} [PseudoMetricSpace E]
    {x : E} {r : ℝ} (hcompl : (ball x r)ᶜ.Nonempty) (z : E) :
    r - dist x z ≤ infDist z (ball x r)ᶜ := by
  apply (le_infDist hcompl).mpr
  intro w hw
  have hw' : r ≤ dist w x := le_of_not_gt hw
  have ht := dist_triangle w z x
  rw [dist_comm w z, dist_comm z x] at ht
  linarith

/-- A constant-speed minimizing segment from an interior point toward the center stays
inside the ball. Boundary distance dominates elapsed distance and half the starting
boundary distance throughout the segment. -/
theorem metric_segment_boundary_bounds {E : Type*} [MetricSpace E]
    {x z : E} {r : ℝ} (hz : z ∈ ball x r) (hcompl : (ball x r)ᶜ.Nonempty)
    {γ : Icc (0 : ℝ) 1 → E}
    (hzero : γ ⟨0, by norm_num⟩ = z) (hone : γ ⟨1, by norm_num⟩ = x)
    (hγ : ∀ s t, dist (γ s) (γ t) = dist z x * dist s t) :
    ∀ t, γ t ∈ ball x r ∧ dist z (γ t) ≤ infDist (γ t) (ball x r)ᶜ ∧
      infDist z (ball x r)ᶜ / 2 ≤ infDist (γ t) (ball x r)ᶜ := by
  intro t
  let o : Icc (0 : ℝ) 1 := ⟨0, by norm_num⟩
  let e : Icc (0 : ℝ) 1 := ⟨1, by norm_num⟩
  have hot : dist o t = (t : ℝ) := by
    change |0 - (t : ℝ)| = (t : ℝ)
    rw [zero_sub, abs_neg, abs_of_nonneg t.2.1]
  have hte : dist t e = 1 - (t : ℝ) := by
    change |(t : ℝ) - 1| = 1 - (t : ℝ)
    rw [abs_of_nonpos (sub_nonpos.mpr t.2.2)]
    ring
  have hstart := hγ o t
  rw [show γ o = z from hzero, hot] at hstart
  have hend := hγ t e
  rw [show γ e = x from hone, hte, dist_comm (γ t) x] at hend
  have hD : dist z x < r := mem_ball.mp hz
  have hprod : dist z x * (t : ℝ) ≤ dist z x := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left t.2.2 (dist_nonneg : 0 ≤ dist z x)
  have hlower := sub_dist_le_infDist_compl_ball hcompl (γ t)
  rw [hend] at hlower
  have hδ : dist z (γ t) ≤ infDist (γ t) (ball x r)ᶜ := by
    rw [hstart]
    nlinarith
  have hleft : infDist z (ball x r)ᶜ ≤ infDist (γ t) (ball x r)ᶜ + dist z (γ t) :=
    infDist_le_infDist_add_dist
  refine ⟨?_, hδ, by linarith⟩
  apply mem_ball.mpr
  rw [dist_comm, hend]
  nlinarith [mul_nonneg (dist_nonneg : 0 ≤ dist z x) t.2.1]

end HeatKernel
