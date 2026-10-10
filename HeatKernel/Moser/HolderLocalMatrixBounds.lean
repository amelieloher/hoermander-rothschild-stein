-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.HolderMatrixCylinder
public import HeatKernel.Moser.MeanValueMatrixCompactBounds
public import HeatKernel.Moser.MeanValueInteriorCylinders
import Mathlib.Tactic

/-! # Bounded parabolic neighborhoods of signed weak solutions -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein Filter Metric
namespace HeatKernel
set_option backward.isDefEq.respectTransparency false

/-- Every interior point of a signed weak solution has a parabolic neighborhood
whose doubled cylinder carries finite upper and lower essential bounds. -/
theorem IsLocalWeakSolution.exists_bounded_parabolic_neighborhood {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    {coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ}
    {I : Opens ℝ} {U : Opens (Fin N → ℝ)} {u : ℝ → (Fin N → ℝ) → ℝ}
    (hu : IsLocalWeakSolution G hq hqpos hw hspan coeff I U u)
    (ha : ∀ i j, Measurable (fun z : ℝ × (Fin N → ℝ) => coeff z.1 z.2 i j))
    {ell upper : ℝ} (hell : 0 < ell) (hupper : 0 ≤ upper)
    (hquad : ∀ᵐ z : ℝ × (Fin N → ℝ) ∂volume,
      (∀ i j, coeff z.1 z.2 i j = coeff z.1 z.2 j i) ∧ ∀ ξ : Fin q → ℝ,
        ell * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ∧
        ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ≤ upper * ∑ i, ξ i ^ 2)
    (z : ℝ × CarnotPoint G hq hqpos hspan) (hz : z ∈ (I : Set ℝ) ×ˢ (U : Set (Fin N → ℝ))) :
    ∃ t r : ℝ, 0 < r ∧ z ∈ parabolicCylinder z.2 t r ∧
      IsLocalWeakSolution G hq hqpos hw hspan coeff
        ⟨Ioo (t - (2 * r) ^ 2) t, isOpen_Ioo⟩
        ⟨horizontalBall (G.horizontalFields hq) z.2 (2 * r),
          isOpen_horizontalBall G hq hqpos hspan z.2 (2 * r)⟩ u ∧
      IsBoundedUnder (· ≤ ·)
        (ae ((CarnotPoint.spaceTimeVolume G hq hqpos hspan).restrict (parabolicCylinder z.2 t (2 * r))))
        (Function.uncurry u) ∧
      IsBoundedUnder (· ≥ ·)
        (ae ((CarnotPoint.spaceTimeVolume G hq hqpos hspan).restrict (parabolicCylinder z.2 t (2 * r))))
        (Function.uncurry u) := by
  have hUopen : IsOpen (show Set (CarnotPoint G hq hqpos hspan) from (U : Set (Fin N → ℝ))) := U.isOpen
  obtain ⟨δ, hδ, htime⟩ := Metric.isOpen_iff.mp I.isOpen z.1 hz.1
  obtain ⟨ε, hε, hspace⟩ := Metric.isOpen_iff.mp hUopen z.2 hz.2
  obtain ⟨r, hr, hrε, hrδ⟩ := exists_positive_radius_for_cylinder_gaps
    (show (0 : ℝ) < ε / 4 by positivity) (show (0 : ℝ) < δ / 16 by positivity)
  have hrε' : r ≤ ε / 4 := by simpa only [sub_zero] using hrε
  have hrδ' : r ^ 2 ≤ δ / 16 := by simpa only [sub_zero] using hrδ
  let t := z.1 + r ^ 2 / 2
  let bottom := z.1 - 5 * r ^ 2
  have hI : Icc bottom t ⊆ (I : Set ℝ) := by
    intro s hs
    apply htime
    rw [mem_ball, Real.dist_eq, abs_lt]
    dsimp only [bottom, t] at hs
    constructor <;> nlinarith [hs.1, hs.2]
  have hU : (@closedBall (CarnotPoint G hq hqpos hspan) _ z.2 (3 * r) :
      Set (Fin N → ℝ)) ⊆ (U : Set (Fin N → ℝ)) := by
    intro y hy
    apply hspace
    exact mem_ball.mpr ((mem_closedBall.mp hy).trans_lt (by linarith))
  have hb := hu.isBoundedUnder_nested_cylinder G hq hqpos hspan hw
    ha hell hupper hquad z.2
    (show bottom < t - (2 * r) ^ 2 by dsimp only [bottom, t]; nlinarith [sq_pos_of_pos hr])
    (show 2 * r < 3 * r by linarith) hI hU
  have hspace' : horizontalBall (G.horizontalFields hq) z.2 (2 * r) ⊆
      (U : Set (Fin N → ℝ)) := by
    rw [← CarnotPoint.coordinateBall_eq_horizontalBall G hq hqpos hspan]
    exact ((ball_subset_ball (by linarith : 2 * r ≤ 3 * r)).trans ball_subset_closedBall).trans hU
  have htime' : Ioo (t - (2 * r) ^ 2) t ⊆ (I : Set ℝ) := by
    intro s hs
    apply hI
    dsimp only [bottom, t] at hs ⊢
    constructor <;> nlinarith [hs.1, hs.2, sq_pos_of_pos hr]
  refine ⟨t, r, hr, ⟨?_, mem_ball_self hr⟩, hu.mono htime' hspace', ?_⟩
  · dsimp only [t]
    constructor <;> nlinarith [sq_pos_of_pos hr]
  · simpa only [parabolicCylinder_eq_horizontal G hq hqpos hspan,
      CarnotPoint.spaceTimeVolume_eq_coordinate] using hb

end HeatKernel
