-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.CarnotWhitneyRadiusSum

/-! Finite index sets for all Whitney balls meeting a radial segment. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric MeasureTheory RothschildStein
open scoped ENNReal BigOperators Classical

namespace HeatKernel.CarnotPoint

/-- All selected balls meeting a radial metric segment form a finite index set with
the quantitative radius bound. The index set retains the original selected centers. -/
theorem exists_finite_boundaryBall_meeting_family {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {x z : CarnotPoint G hq hqpos hspan} {r κ : ℝ}
    {C : Set (CarnotPoint G hq hqpos hspan)} (hr : 0 < r) (hκ : 10 < κ)
    (hz : z ∈ ball x r) (hCU : C ⊆ ball x r)
    (hdisj : C.PairwiseDisjoint fun w => ball w (infDist w (ball x r)ᶜ / κ))
    (k : ℕ) (hk : 0 < k) (hscale : 2 * κ + 22 ≤ (k : ℝ))
    {γ : Icc (0 : ℝ) 1 → CarnotPoint G hq hqpos hspan}
    (hzero : γ ⟨0, by norm_num⟩ = z) (hone : γ ⟨1, by norm_num⟩ = x)
    (hγ : ∀ t u, dist (γ t) (γ u) = dist z x * dist t u) :
    ∃ s : Finset C,
      (∀ w : C, w ∈ s ↔
        (ball w.val (5 * (infDist w.val (ball x r)ᶜ / κ)) ∩ range γ).Nonempty) ∧
      (∑ w ∈ s, infDist w.val (ball x r)ᶜ / κ) ≤
        2 * (k ^ G.homogeneousDimension : ℕ) * (2 * r / κ) := by
  classical
  let T : Set C := {w | (ball w.val (5 * (infDist w.val (ball x r)ᶜ / κ)) ∩ range γ).Nonempty}
  have hi := finite_boundaryBalls_meeting_segment G hq hqpos hspan hw hr hκ hz
    hCU hdisj hzero hone hγ
  have ht : T.Finite := by
    have hh := hi.preimage (f := fun w : C => w.val)
      (fun _ _ _ _ h => Subtype.ext h)
    simpa only [boundaryBallsMeetingPath, Set.preimage_ofPred_eq, Subtype.coe_prop,
      true_and] using hh
  let s := ht.toFinset
  have hs : ∀ w : C, w ∈ s ↔
      (ball w.val (5 * (infDist w.val (ball x r)ᶜ / κ)) ∩ range γ).Nonempty :=
    fun _ => ht.mem_toFinset
  refine ⟨s, hs, ?_⟩
  let t := s.image (fun w : C => w.val)
  have htU : ∀ w ∈ t, w ∈ ball x r := by
    intro w hw'
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hw'
    exact hCU v.property
  have htmeet : ∀ w ∈ t,
      (ball w (5 * (infDist w (ball x r)ᶜ / κ)) ∩ range γ).Nonempty := by
    intro w hw'
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw'
    exact (hs v).mp hv
  have htdisj : (t : Set (CarnotPoint G hq hqpos hspan)).PairwiseDisjoint
      fun w => ball w (infDist w (ball x r)ᶜ / κ) := by
    intro w hw' v hv' hwv
    obtain ⟨w', _, rfl⟩ := Finset.mem_image.mp hw'
    obtain ⟨v', _, rfl⟩ := Finset.mem_image.mp hv'
    exact hdisj w'.property v'.property hwv
  have hb := sum_boundaryBall_radii_le_of_radial_meeting G hq hqpos hspan hw hr hκ
    hz t htU htdisj k hk hscale hzero hone hγ htmeet
  have heq : (∑ w ∈ t, infDist w (ball x r)ᶜ / κ) =
      ∑ w ∈ s, infDist w.val (ball x r)ᶜ / κ :=
    Finset.sum_image fun _ _ _ _ h => Subtype.ext h
  rwa [heq] at hb

end HeatKernel.CarnotPoint
