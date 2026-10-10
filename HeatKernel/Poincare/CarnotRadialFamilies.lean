-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.CarnotMeetingFamily
public import HeatKernel.Poincare.CarnotWhitneyShadows
public import HeatKernel.Poincare.CarnotSegment

/-! Simultaneous finite radial families with radius and shadow bounds. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric MeasureTheory RothschildStein
open scoped ENNReal BigOperators Classical

namespace HeatKernel.CarnotPoint

/-- Choosing radial segments and all their meeting balls simultaneously gives finite
families with uniform radius sums and controlled shadows. -/
theorem exists_finite_radial_families_with_shadow_bounds {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {x : CarnotPoint G hq hqpos hspan} {r κ : ℝ}
    (C : Set (CarnotPoint G hq hqpos hspan)) (hr : 0 < r) (hκ : 10 < κ)
    (hCU : C ⊆ ball x r)
    (hdisj : C.PairwiseDisjoint fun w => ball w (infDist w (ball x r)ᶜ / κ))
    (k : ℕ) (hk : 0 < k) (hscale : 2 * κ + 22 ≤ (k : ℝ)) :
    ∃ (γ : C → Icc (0 : ℝ) 1 → CarnotPoint G hq hqpos hspan) (chain : C → Finset C),
      (∀ z : C, γ z ⟨0, by norm_num⟩ = z.val ∧ γ z ⟨1, by norm_num⟩ = x ∧
        (∀ t u, dist (γ z t) (γ z u) = dist z.val x * dist t u) ∧
        (∀ w : C, w ∈ chain z ↔
          (ball w.val (5 * (infDist w.val (ball x r)ᶜ / κ)) ∩ range (γ z)).Nonempty) ∧
        (∑ w ∈ chain z, infDist w.val (ball x r)ᶜ / κ) ≤
          2 * (k ^ G.homogeneousDimension : ℕ) * (2 * r / κ)) ∧
      (∀ w : C, (∑' z : {z : C | w ∈ chain z},
          CarnotPoint.volume G hq hqpos hspan
            (ball z.val.val (infDist z.val.val (ball x r)ᶜ / κ))) ≤
        ENNReal.ofReal ((κ + 13) ^ G.homogeneousDimension) *
          CarnotPoint.volume G hq hqpos hspan
            (ball w.val (infDist w.val (ball x r)ᶜ / κ))) := by
  classical
  have hex := fun z : C => exists_metric_segment G hq hqpos hspan hw z.val x
  choose γ hzero hone hγ using hex
  have hs := fun z : C => exists_finite_boundaryBall_meeting_family G hq hqpos hspan hw
    hr hκ (hCU z.property) hCU hdisj k hk hscale (hzero z) (hone z) (hγ z)
  choose chain hmem hradius using hs
  refine ⟨γ, chain, fun z => ⟨hzero z, hone z, hγ z, hmem z, hradius z⟩, ?_⟩
  intro w
  have heq : {z : C | w ∈ chain z} =
      {z : C | (ball w.val (5 * (infDist w.val (ball x r)ᶜ / κ)) ∩ range (γ z)).Nonempty} :=
    Set.ext fun z => hmem z w
  rw [heq]
  exact tsum_measure_boundaryBall_radial_shadow_le G hq hqpos hspan hw hr hκ hCU
    w.property hdisj γ hzero hone hγ

end HeatKernel.CarnotPoint
