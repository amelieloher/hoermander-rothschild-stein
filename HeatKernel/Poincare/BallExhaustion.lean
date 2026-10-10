-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.CarnotBallCoordinates
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter Metric RothschildStein
open scoped ENNReal Topology
namespace HeatKernel

/-- Every positive radius is the limit of an increasing sequence of strictly smaller
positive radii. -/
theorem exists_increasing_positive_radii {r : ℝ} (hr : 0 < r) :
    ∃ s : ℕ → ℝ, (∀ n, 0 < s n ∧ s n < r) ∧ Monotone s ∧ Tendsto s atTop (𝓝 r) := by
  let τ := fun n : ℕ => 1 / ((n : ℝ) + 1)
  have htpos : ∀ n, 0 < τ n := fun n => by dsimp [τ]; positivity
  have htone : ∀ n, τ n ≤ 1 := fun n => by
    dsimp only [τ]
    simpa only [div_one] using one_div_le_one_div_of_le zero_lt_one
      (show (1 : ℝ) ≤ (n : ℝ) + 1 by have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n; linarith)
  refine ⟨fun n => r * (1 - τ n / 2), ?_, ?_, ?_⟩
  · intro n
    constructor
    · exact mul_pos hr (by linarith [htone n])
    · nlinarith [htpos n]
  · intro m n hmn
    have hτ : τ n ≤ τ m := one_div_le_one_div_of_le (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hmn 1)
    exact mul_le_mul_of_nonneg_left (by linarith) hr.le
  · have ht : Tendsto τ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [zero_div, sub_zero, mul_one] using
      ((tendsto_const_nhds (x := r)).mul ((tendsto_const_nhds (x := (1 : ℝ))).sub (ht.div_const 2)))

/-- A radius exhaustion exhausts the horizontal ball itself. -/
theorem iUnion_horizontalBall_eq_of_tendsto {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)) (x : Fin N → ℝ)
    {s : ℕ → ℝ} {r : ℝ} (hle : ∀ n, s n ≤ r) (hs : Tendsto s atTop (𝓝 r)) :
    (⋃ n, horizontalBall X x (s n)) = horizontalBall X x r := by
  ext y
  constructor
  · intro hy
    obtain ⟨n, hn⟩ := mem_iUnion.mp hy
    exact lt_of_lt_of_le hn (ENNReal.ofReal_le_ofReal (hle n))
  · intro hy
    have H := (tendsto_order.1 (ENNReal.tendsto_ofReal hs)).1
      (horizontalL2Distance X x y) hy
    obtain ⟨n, hn⟩ := H.exists
    exact mem_iUnion.mpr ⟨n, hn⟩

/-- Every strictly smaller concentric horizontal ball has closure inside the original
ball, by coordinate transport of metric balls. -/
theorem closure_horizontalBall_subset_of_radius_lt {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (x : Fin N → ℝ) {s r : ℝ} (hsr : s < r) :
    closure (horizontalBall (G.horizontalFields hq) x s) ⊆
      horizontalBall (G.horizontalFields hq) x r := by
  let z : CarnotPoint G hq hqpos hspan := x
  have hb : closure (ball z s) ⊆ ball z r :=
    closure_ball_subset_closedBall.trans (fun y hy =>
      Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hy).trans_lt hsr))
  have hi := Set.image_mono (f := CarnotPoint.coordinateHomeomorph G hq hqpos hspan) hb
  rwa [CarnotPoint.coordinateHomeomorph_image_closure_ball G hq hqpos hspan,
    CarnotPoint.coordinateHomeomorph_image_ball G hq hqpos hspan] at hi

end HeatKernel
