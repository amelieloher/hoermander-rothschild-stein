-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.WeakPoincareNorm
public import HeatKernel.Poincare.WhitneyInterior
public import HeatKernel.Poincare.CarnotWhitneyCover
public import HeatKernel.Poincare.CarnotBallCoordinates

/-! Smooth weak Poincaré estimates on interior Whitney averaging balls. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric MeasureTheory RothschildStein
open scoped ENNReal

namespace HeatKernel

/-- Applying weak Poincaré to a twentyfold Whitney ball uses only continuous
differentiability on the original ball, because its eightyfold closure stays inside. -/
theorem eLpNorm_weak_horizontalPoincare_on_boundaryBall {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {x z : CarnotPoint G hq hqpos hspan} {r κ p : ℝ} (hr : 0 < r) (hκ : 80 < κ)
    (hz : z ∈ ball x r) (hp : 1 ≤ p) (u : (Fin N → ℝ) → ℝ)
    (hu : ContDiffOn ℝ 1 u (horizontalBall (G.horizontalFields hq) x r)) :
    let a := infDist z (ball x r)ᶜ / κ
    eLpNorm (fun y => u y - ⨍ w in horizontalBall (G.horizontalFields hq) z (20 * a), u w)
      (ENNReal.ofReal p) (volume.restrict (horizontalBall (G.horizontalFields hq) z (20 * a))) ≤
      ENNReal.ofReal (((2 : ℝ) ^ G.homogeneousDimension) ^ (1 / p) * (3 * (20 * a))) *
        eLpNorm (horizontalGradientNorm (G.horizontalFields hq) u) (ENNReal.ofReal p)
          (volume.restrict (horizontalBall (G.horizontalFields hq) z (80 * a))) := by
  let a := infDist z (ball x r)ᶜ / κ
  let x₀ : Fin N → ℝ := x
  let z₀ : Fin N → ℝ := z
  obtain ⟨y, hy⟩ := CarnotPoint.exists_dist_eq G hq hqpos hspan hw x hr
  have hcompl : (ball x r)ᶜ.Nonempty := by
    refine ⟨y, ?_⟩
    change ¬ dist y x < r
    rw [dist_comm, hy]
    exact lt_irrefl r
  have ha : 0 < a := div_pos
    ((isOpen_ball.isClosed_compl.notMem_iff_infDist_pos hcompl).mp (by simpa using hz))
    (by linarith)
  have hclosure : closure (ball z (80 * a)) ⊆ ball x r :=
    closure_ball_subset_closedBall.trans
      (closedBall_boundaryRadius_subset isOpen_ball hcompl hz (by linarith) hκ)
  have hsub : closure (horizontalBall (G.horizontalFields hq) z₀ (4 * (20 * a))) ⊆
      horizontalBall (G.horizontalFields hq) x₀ r := by
    have hi : CarnotPoint.coordinateHomeomorph G hq hqpos hspan '' closure (ball z (80 * a)) ⊆
        CarnotPoint.coordinateHomeomorph G hq hqpos hspan '' ball x r := Set.image_mono hclosure
    rw [CarnotPoint.coordinateHomeomorph_image_closure_ball G hq hqpos hspan z (80 * a),
      CarnotPoint.coordinateHomeomorph_image_ball G hq hqpos hspan x r] at hi
    simpa only [show 4 * (20 * a) = 80 * a by ring] using hi
  have hh := eLpNorm_weak_horizontalPoincare G hq hqpos hspan hw z₀
    (mul_pos (by norm_num : (0 : ℝ) < 20) ha) hp u
    (horizontalBall (G.horizontalFields hq) x₀ r)
    (isOpen_horizontalBall G hq hqpos hspan x₀ r) hsub hu
  rw [show 4 * (20 * a) = 80 * a by ring] at hh
  exact hh

end HeatKernel
