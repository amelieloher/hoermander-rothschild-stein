-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.RadialRadiusSum
public import HeatKernel.Poincare.BallBoundary

/-! Radius-sum estimates for Whitney balls meeting radial minimizing segments. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal BigOperators

namespace HeatKernel

/-- Every finite collection of disjoint Whitney balls meeting one radial segment has a
controlled radius sum, from exact homogeneous volume and a point on the outer sphere. -/
theorem sum_boundaryBall_radii_le_of_radial_meeting {E : Type*} [MetricSpace E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) (Q : ℕ) (v : ℝ≥0∞)
    (hv0 : v ≠ 0) (hvtop : v ≠ ⊤)
    (hvolume : ∀ x : E, ∀ r : ℝ, 0 < r → μ (ball x r) = ENNReal.ofReal (r ^ Q) * v)
    {x z y : E} {r κ : ℝ} (hr : 0 < r) (hκ : 10 < κ)
    (hy : dist x y = r) (hz : z ∈ ball x r)
    (s : Finset E) (hs : ∀ w ∈ s, w ∈ ball x r)
    (hdisj : (s : Set E).PairwiseDisjoint fun w => ball w (infDist w (ball x r)ᶜ / κ))
    (k : ℕ) (hk : 0 < k) (hscale : 2 * κ + 22 ≤ (k : ℝ))
    {γ : Icc (0 : ℝ) 1 → E}
    (hzero : γ ⟨0, by norm_num⟩ = z) (hone : γ ⟨1, by norm_num⟩ = x)
    (hγ : ∀ t u, dist (γ t) (γ u) = dist z x * dist t u)
    (hmeet : ∀ w ∈ s, (ball w (5 * (infDist w (ball x r)ᶜ / κ)) ∩ range γ).Nonempty) :
    (∑ w ∈ s, infDist w (ball x r)ᶜ / κ) ≤
      2 * (k ^ Q : ℕ) * (2 * r / κ) := by
  have hkpos : 0 < κ := by linarith
  have hcompl : (ball x r)ᶜ.Nonempty := by
    refine ⟨y, ?_⟩
    change ¬ dist y x < r
    rw [dist_comm, hy]
    exact lt_irrefl r
  apply sum_radii_le_of_radial_ball_packing μ Q v hv0 hvtop hvolume s id
    (fun w => infDist w (ball x r)ᶜ / κ) z (div_pos (by linarith) hkpos)
    (by linarith) k hk hscale hdisj
  · intro w hw
    exact div_pos ((isOpen_ball.isClosed_compl.notMem_iff_infDist_pos hcompl).mp
      (by simpa using hs w hw)) hkpos
  · intro w hw
    exact div_le_div_of_nonneg_right (infDist_ball_compl_le_two_mul (hs w hw) hy) hkpos.le
  · intro w hw
    exact (boundaryBall_bounds_of_radial_segment_meeting hκ hz hcompl hzero hone hγ
      (hmeet w hw)).2.1

end HeatKernel
