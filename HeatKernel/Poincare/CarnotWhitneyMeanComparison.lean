-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.WhitneyMeanComparison
public import HeatKernel.Poincare.CarnotWhitneyCover
public import HeatKernel.Poincare.CarnotBallVolume

/-! Neighboring averaging constants on homogeneous horizontal Whitney balls. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric MeasureTheory RothschildStein
open scoped ENNReal

namespace HeatKernel

/-- Normalized oscillation bounds on neighboring horizontal averaging balls control
both constants with the exact homogeneous volume comparison factor. -/
theorem ofReal_abs_sub_le_of_horizontal_boundaryBall_oscillation_bounds {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {x z w : CarnotPoint G hq hqpos hspan} {r κ a b : ℝ} (hr : 0 < r) (hκ : 80 < κ)
    (hz : z ∈ ball x r) (hwball : w ∈ ball x r)
    (haeq : a = infDist z (ball x r)ᶜ / κ) (hbeq : b = infDist w (ball x r)ᶜ / κ)
    (hmeet : (ball z (5 * a) ∩ ball w (5 * b)).Nonempty)
    (u : (Fin N → ℝ) → ℝ) (c d : ℝ) {p : ℝ≥0∞} (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    (e₁ e₂ : ℝ≥0∞)
    (hfirst : eLpNorm (fun y => u y - c) p
      (volume.restrict (horizontalBall (G.horizontalFields hq) z (20 * a))) ≤
      e₁ * volume (horizontalBall (G.horizontalFields hq) z a) ^ (1 / p.toReal))
    (hsecond : eLpNorm (fun y => u y - d) p
      (volume.restrict (horizontalBall (G.horizontalFields hq) w (20 * b))) ≤
      e₂ * volume (horizontalBall (G.horizontalFields hq) w b) ^ (1 / p.toReal)) :
    ENNReal.ofReal |c - d| ≤ ((2 : ℝ≥0∞) ^ G.homogeneousDimension) ^ (1 / p.toReal) *
      (e₁ + e₂) := by
  let μ := CarnotPoint.volume G hq hqpos hspan
  let v := MeasureTheory.volume (horizontalBall (G.horizontalFields hq) 0 1)
  have hv0 : v ≠ 0 := (volume_horizontalBall_pos G hq hqpos hspan 0 zero_lt_one).ne'
  have hvtop : v ≠ ⊤ := (volume_horizontalBall_lt_top G hq hqpos hspan hw 0 zero_le_one).ne
  have hvolume : ∀ y : CarnotPoint G hq hqpos hspan, ∀ s : ℝ, 0 < s →
      μ (ball y s) = ENNReal.ofReal (s ^ G.homogeneousDimension) * v :=
    fun y s hs => CarnotPoint.volume_ball G hq hqpos hspan hw y hs
  obtain ⟨y, hy⟩ := CarnotPoint.exists_dist_eq G hq hqpos hspan hw x hr
  have hcompl : (ball x r)ᶜ.Nonempty := by
    refine ⟨y, ?_⟩
    change ¬ dist y x < r
    rw [dist_comm, hy]
    exact lt_irrefl r
  have ha : 0 < a := by
    rw [haeq]
    exact div_pos ((isOpen_ball.isClosed_compl.notMem_iff_infDist_pos hcompl).mp
      (by simpa using hz)) (by linarith)
  have hb : 0 < b := by
    rw [hbeq]
    exact div_pos ((isOpen_ball.isClosed_compl.notMem_iff_infDist_pos hcompl).mp
      (by simpa using hwball)) (by linarith)
  have hcomp : a ≤ 2 * b ∧ b ≤ 2 * a := by
    rw [haeq, hbeq] at hmeet ⊢
    exact boundaryBall_radii_comparable_of_dilates_intersect (ball x r)
      (by norm_num : (0 : ℝ) ≤ 5) (by linarith) hmeet
  have hfirst' : eLpNorm (fun y : CarnotPoint G hq hqpos hspan => u y - c) p
      (μ.restrict (ball z (20 * a))) ≤ e₁ * μ (ball z a) ^ (1 / p.toReal) := by
    rw [CarnotPoint.ball_eq_horizontalBall G hq hqpos hspan z (20 * a),
      CarnotPoint.ball_eq_horizontalBall G hq hqpos hspan z a]
    exact hfirst
  have hsecond' : eLpNorm (fun y : CarnotPoint G hq hqpos hspan => u y - d) p
      (μ.restrict (ball w (20 * b))) ≤ e₂ * μ (ball w b) ^ (1 / p.toReal) := by
    rw [CarnotPoint.ball_eq_horizontalBall G hq hqpos hspan w (20 * b),
      CarnotPoint.ball_eq_horizontalBall G hq hqpos hspan w b]
    exact hsecond
  exact ofReal_abs_sub_le_of_neighboring_ball_eLpNorm_bounds μ G.homogeneousDimension v
    hv0 hvtop hvolume (fun y => u y) c d z w ha hb hcomp.1 hcomp.2 hmeet hp hptop e₁ e₂
    hfirst' hsecond'

end HeatKernel
