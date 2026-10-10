-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.CarnotWhitneyCover
public import HeatKernel.Poincare.CarnotBallVolume
public import HeatKernel.Poincare.FiniteWhitneyPath
public import HeatKernel.Poincare.RadialWhitneyChain

/-! Finite radial meeting families in homogeneous horizontal balls. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric MeasureTheory RothschildStein
open scoped ENNReal

namespace HeatKernel.CarnotPoint

/-- The Whitney balls meeting a radial minimizing segment in a horizontal ball form a
finite family, using the exact horizontal volume and sphere geometry. -/
theorem finite_boundaryBalls_meeting_segment {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {x z : CarnotPoint G hq hqpos hspan} {r κ : ℝ}
    {C : Set (CarnotPoint G hq hqpos hspan)} (hr : 0 < r) (hκ : 10 < κ)
    (hz : z ∈ ball x r) (hCU : C ⊆ ball x r)
    (hdisj : C.PairwiseDisjoint fun w => ball w (infDist w (ball x r)ᶜ / κ))
    {γ : Icc (0 : ℝ) 1 → CarnotPoint G hq hqpos hspan}
    (hzero : γ ⟨0, by norm_num⟩ = z) (hone : γ ⟨1, by norm_num⟩ = x)
    (hγ : ∀ s t, dist (γ s) (γ t) = dist z x * dist s t) :
    (boundaryBallsMeetingPath C (ball x r) κ γ).Finite := by
  let μ := CarnotPoint.volume G hq hqpos hspan
  let v := MeasureTheory.volume (horizontalBall (G.horizontalFields hq) 0 1)
  have hv0 : v ≠ 0 := (volume_horizontalBall_pos G hq hqpos hspan 0 zero_lt_one).ne'
  have hvtop : v ≠ ⊤ := (volume_horizontalBall_lt_top G hq hqpos hspan hw 0 zero_le_one).ne
  have hvolume : ∀ w : CarnotPoint G hq hqpos hspan, ∀ s : ℝ, 0 < s →
      μ (ball w s) = ENNReal.ofReal (s ^ G.homogeneousDimension) * v :=
    fun w s hs => volume_ball G hq hqpos hspan hw w hs
  obtain ⟨y, hy⟩ := exists_dist_eq G hq hqpos hspan hw x hr
  have hcompl : (ball x r)ᶜ.Nonempty := by
    refine ⟨y, ?_⟩
    change ¬ dist y x < r
    rw [dist_comm, hy]
    exact lt_irrefl r
  have hradius : ∀ w ∈ C, infDist w (ball x r)ᶜ / κ ≤ r := by
    intro w hwC
    apply (div_le_iff₀ (show 0 < κ by linarith)).mpr
    have hb := infDist_ball_compl_le_two_mul (hCU hwC) hy
    have hm := mul_nonneg hr.le (show 0 ≤ κ - 2 by linarith)
    nlinarith
  exact finite_boundaryBalls_meeting_segment_of_radius_bound μ G.homogeneousDimension v
    hv0 hvtop hvolume hκ hz hcompl hCU hdisj hradius hzero hone hγ

end HeatKernel.CarnotPoint
