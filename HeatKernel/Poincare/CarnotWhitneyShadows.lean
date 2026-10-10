-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.CarnotWhitneyPath
public import HeatKernel.Poincare.RadialShadows

/-! Full radial shadows of Whitney balls in homogeneous horizontal metrics. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric MeasureTheory RothschildStein
open scoped ENNReal BigOperators

namespace HeatKernel.CarnotPoint

/-- The full radial shadow of a selected Whitney ball has controlled total measure.
Every simple chain supported on those radial segments inherits the same shadow bound. -/
theorem tsum_measure_boundaryBall_radial_shadow_le {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {x w : CarnotPoint G hq hqpos hspan} {r κ : ℝ}
    {C : Set (CarnotPoint G hq hqpos hspan)} (hr : 0 < r) (hκ : 10 < κ)
    (hCU : C ⊆ ball x r) (hwC : w ∈ C)
    (hdisj : C.PairwiseDisjoint fun z => ball z (infDist z (ball x r)ᶜ / κ))
    (γ : C → Icc (0 : ℝ) 1 → CarnotPoint G hq hqpos hspan)
    (hzero : ∀ z : C, γ z ⟨0, by norm_num⟩ = z.val)
    (hone : ∀ z : C, γ z ⟨1, by norm_num⟩ = x)
    (hγ : ∀ z : C, ∀ t u, dist (γ z t) (γ z u) = dist z.val x * dist t u) :
    (∑' z : {z : C | (ball w (5 * (infDist w (ball x r)ᶜ / κ)) ∩ range (γ z)).Nonempty},
      CarnotPoint.volume G hq hqpos hspan
        (ball z.val.val (infDist z.val.val (ball x r)ᶜ / κ))) ≤
      ENNReal.ofReal ((κ + 13) ^ G.homogeneousDimension) *
        CarnotPoint.volume G hq hqpos hspan (ball w (infDist w (ball x r)ᶜ / κ)) := by
  let μ := CarnotPoint.volume G hq hqpos hspan
  let v := MeasureTheory.volume (horizontalBall (G.horizontalFields hq) 0 1)
  have hvolume : ∀ z : CarnotPoint G hq hqpos hspan, ∀ s : ℝ, 0 < s →
      μ (ball z s) = ENNReal.ofReal (s ^ G.homogeneousDimension) * v :=
    fun z s hs => volume_ball G hq hqpos hspan hw z hs
  obtain ⟨y, hy⟩ := exists_dist_eq G hq hqpos hspan hw x hr
  have hcompl : (ball x r)ᶜ.Nonempty := by
    refine ⟨y, ?_⟩
    change ¬ dist y x < r
    rw [dist_comm, hy]
    exact lt_irrefl r
  exact tsum_measure_boundaryBall_radial_shadow_le_of_volume μ G.homogeneousDimension v
    hvolume hκ hcompl hCU hwC hdisj γ hzero hone hγ

end HeatKernel.CarnotPoint
