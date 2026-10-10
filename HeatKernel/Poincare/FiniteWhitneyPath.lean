-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.BoundedBallPacking
public import HeatKernel.Poincare.WhitneyPathBounds

/-! Finiteness of the Whitney balls meeting a radial minimizing segment. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal

namespace HeatKernel

/-- A ball of radius at most r centered in B(x,r) lies inside B(x,2r). -/
theorem ball_subset_double_of_center_mem {E : Type*} [PseudoMetricSpace E]
    {x z : E} {r a : ℝ} (hz : z ∈ ball x r) (ha : a ≤ r) : ball z a ⊆ ball x (2 * r) := by
  intro y hy
  apply mem_ball.mpr
  calc
    dist y x ≤ dist y z + dist z x := dist_triangle y z x
    _ < a + r := add_lt_add (mem_ball.mp hy) (mem_ball.mp hz)
    _ ≤ 2 * r := by linarith

/-- In exact homogeneous volume, the selected boundary-distance balls meeting a radial
segment form a finite set. The upper radius bound and volume formula are explicit inputs. -/
theorem finite_boundaryBalls_meeting_segment_of_radius_bound {E : Type*} [MetricSpace E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) (Q : ℕ) (v : ℝ≥0∞)
    (hv0 : v ≠ 0) (hvtop : v ≠ ⊤)
    (hvolume : ∀ x : E, ∀ s : ℝ, 0 < s → μ (ball x s) = ENNReal.ofReal (s ^ Q) * v)
    {x z : E} {r κ : ℝ} {C : Set E} (hκ : 10 < κ) (hz : z ∈ ball x r)
    (hcompl : (ball x r)ᶜ.Nonempty) (hCU : C ⊆ ball x r)
    (hdisj : C.PairwiseDisjoint fun w => ball w (infDist w (ball x r)ᶜ / κ))
    (hradius : ∀ w ∈ C, infDist w (ball x r)ᶜ / κ ≤ r)
    {γ : Icc (0 : ℝ) 1 → E}
    (hzero : γ ⟨0, by norm_num⟩ = z) (hone : γ ⟨1, by norm_num⟩ = x)
    (hγ : ∀ s t, dist (γ s) (γ t) = dist z x * dist s t) :
    {w ∈ C | (ball w (5 * (infDist w (ball x r)ᶜ / κ)) ∩ range γ).Nonempty}.Finite := by
  have hk : 0 < κ := by linarith
  have hb : 0 < infDist z (ball x r)ᶜ / κ := div_pos
    ((isOpen_ball.isClosed_compl.notMem_iff_infDist_pos hcompl).mp (by simpa using hz)) hk
  apply finite_of_bounded_homogeneous_ball_packing μ Q v hv0 hvtop hvolume id
    (fun w => infDist w (ball x r)ᶜ / κ) x (div_pos hb (by norm_num : (0 : ℝ) < 3))
    (R := 2 * r)
  · intro w hw u hu hwu
    exact hdisj hw.1 hu.1 hwu
  · intro w hw
    exact (boundaryBall_bounds_of_radial_segment_meeting hκ hz hcompl hzero hone hγ hw.2).1
  · intro w hw
    exact ball_subset_double_of_center_mem (hCU hw.1) (hradius w hw.1)

end HeatKernel
