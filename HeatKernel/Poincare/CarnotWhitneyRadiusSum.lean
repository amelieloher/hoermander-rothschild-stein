-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.CarnotWhitneyPath
public import HeatKernel.Poincare.WhitneyRadiusSum

/-! Homogeneous horizontal instantiation of radial Whitney radius sums. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric MeasureTheory RothschildStein
open scoped ENNReal BigOperators

namespace HeatKernel.CarnotPoint

/-- The radii of any finite disjoint Whitney family meeting a radial horizontal metric
segment have a uniform sum bound in terms of the containing ball radius. -/
theorem sum_boundaryBall_radii_le_of_radial_meeting {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {x z : CarnotPoint G hq hqpos hspan} {r κ : ℝ} (hr : 0 < r) (hκ : 10 < κ)
    (hz : z ∈ ball x r) (s : Finset (CarnotPoint G hq hqpos hspan))
    (hs : ∀ w ∈ s, w ∈ ball x r)
    (hdisj : (s : Set (CarnotPoint G hq hqpos hspan)).PairwiseDisjoint
      fun w => ball w (infDist w (ball x r)ᶜ / κ))
    (k : ℕ) (hk : 0 < k) (hscale : 2 * κ + 22 ≤ (k : ℝ))
    {γ : Icc (0 : ℝ) 1 → CarnotPoint G hq hqpos hspan}
    (hzero : γ ⟨0, by norm_num⟩ = z) (hone : γ ⟨1, by norm_num⟩ = x)
    (hγ : ∀ t u, dist (γ t) (γ u) = dist z x * dist t u)
    (hmeet : ∀ w ∈ s, (ball w (5 * (infDist w (ball x r)ᶜ / κ)) ∩ range γ).Nonempty) :
    (∑ w ∈ s, infDist w (ball x r)ᶜ / κ) ≤
      2 * (k ^ G.homogeneousDimension : ℕ) * (2 * r / κ) := by
  let μ := CarnotPoint.volume G hq hqpos hspan
  let v := MeasureTheory.volume (horizontalBall (G.horizontalFields hq) 0 1)
  have hv0 : v ≠ 0 := (volume_horizontalBall_pos G hq hqpos hspan 0 zero_lt_one).ne'
  have hvtop : v ≠ ⊤ := (volume_horizontalBall_lt_top G hq hqpos hspan hw 0 zero_le_one).ne
  have hvolume : ∀ w : CarnotPoint G hq hqpos hspan, ∀ s : ℝ, 0 < s →
      μ (ball w s) = ENNReal.ofReal (s ^ G.homogeneousDimension) * v :=
    fun w s hs => volume_ball G hq hqpos hspan hw w hs
  obtain ⟨y, hy⟩ := exists_dist_eq G hq hqpos hspan hw x hr
  exact HeatKernel.sum_boundaryBall_radii_le_of_radial_meeting μ G.homogeneousDimension v
    hv0 hvtop hvolume hr hκ hy hz s hs hdisj k hk hscale hzero hone hγ hmeet

end HeatKernel.CarnotPoint
