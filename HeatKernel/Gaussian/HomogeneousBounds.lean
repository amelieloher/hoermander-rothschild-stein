-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Geometry.BallVolume
public import HeatKernel.Poincare.CarnotBallVolume
public import HeatKernel.Geometry.HorizontalSubarc
public import HeatKernel.Gaussian.ScalarBounds
public import HeatKernel.Gaussian.ChainBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.Tactic

/-! # Homogeneous-group volume and chain estimates

The exact horizontal ball-volume formula and the horizontal near-geodesic
construction supply the geometric inputs to the Gaussian estimates.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric RothschildStein
open scoped ENNReal
namespace HeatKernel.Gaussian

/-- The real unit-ball volume is strictly positive and finite. -/
theorem horizontal_unit_ball_volume_real_pos {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q ≤ N) (hqpos : 0 < q) (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1) :
    0 < volume.real (horizontalBall (G.horizontalFields hq) 0 1) := by
  exact ENNReal.toReal_pos
    (volume_horizontalBall_pos G hq hqpos hspan 0 (by norm_num)).ne'
    (volume_horizontalBall_lt_top G hq hqpos hspan hw 0 (by norm_num)).ne

/-- Metric ball volumes on the horizontal space have the exact real-power formula. -/
theorem carnot_volume_ball_eq {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N)
    (hqpos : 0 < q) (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (x : CarnotPoint G hq hqpos hspan) {r : ℝ} (hr : 0 < r) :
    CarnotPoint.volume G hq hqpos hspan (ball x r) =
      ENNReal.ofReal (volume.real (horizontalBall (G.horizontalFields hq) 0 1) *
        r ^ (G.homogeneousDimension : ℝ)) := by
  rw [CarnotPoint.ball_eq_horizontalBall G hq hqpos hspan]
  change volume (horizontalBall (G.horizontalFields hq) x r) = _
  rw [volume_horizontalBall G hq hw x hr, Real.rpow_natCast, measureReal_def,
    ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (volume_horizontalBall_lt_top G hq hqpos hspan hw 0 (by norm_num)).ne]
  exact mul_comm _ _

/-- The distance on the horizontal metric space is the real value of the literal
control-length distance. -/
theorem carnot_dist_eq {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N)
    (hqpos : 0 < q) (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (x y : CarnotPoint G hq hqpos hspan) :
    dist x y = (horizontalL2Distance (G.horizontalFields hq) x y).toReal := dist_edist x y

/-- Any positive integer dominating the quadratic distance ratio is a valid
number of links for the horizontal short-chain construction. -/
theorem exists_carnot_chain_of_count {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N)
    (hqpos : 0 < q) (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (x y : CarnotPoint G hq hqpos hspan) {t : ℝ} (ht : 0 < t)
    (n : ℕ) (hn : 0 < n) (hcount : 64 * dist x y ^ 2 / t ≤ (n : ℝ)) :
    ∃ c : ℕ → CarnotPoint G hq hqpos hspan, c 0 = x ∧ c n = y ∧
      ∀ j, j < n → dist (c j) (c (j + 1)) ≤ (3 / 16 : ℝ) * Real.sqrt (t / n) := by
  by_cases hxy : x = y
  · subst y
    refine ⟨fun _ => x, rfl, rfl, ?_⟩
    intro j _
    simp only [dist_self]
    positivity
  · have hpos : 0 < horizontalL2Distance (G.horizontalFields hq) x y := edist_pos.mpr hxy
    have hfin : horizontalL2Distance (G.horizontalFields hq) x y ≠ ⊤ := edist_ne_top x y
    obtain ⟨l, γ, a, hl, hlen, hx, hy, _, _, hsub⟩ :=
      exists_horizontal_nearGeodesic_with_subarc_bound hpos hfin (by norm_num : (0 : ℝ) < 1 / 2)
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hlength : l ≤ 3 * dist x y / 2 := by
      rw [← carnot_dist_eq G hq hqpos hspan] at hlen
      linarith
    let γc : ℝ → CarnotPoint G hq hqpos hspan := fun s => γ s
    refine ⟨fun j => γc ((j : ℝ) * l / n), ?_, ?_, ?_⟩
    · simpa [γc, CarnotPoint] using hx
    · simpa [γc, CarnotPoint, hnR.ne'] using hy
    · intro j hj
      have hjR : (j : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hj
      have hj0 : 0 ≤ (j : ℝ) := Nat.cast_nonneg _
      have ha : 0 ≤ (j : ℝ) * l / n := by positivity
      have hab : (j : ℝ) * l / n ≤ ((j + 1 : ℕ) : ℝ) * l / n := by
        push_cast
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by linarith) hl.le) hnR.le
      have hbl : ((j + 1 : ℕ) : ℝ) * l / n ≤ l := by
        rw [div_le_iff₀ hnR]
        push_cast
        nlinarith
      have hdist : dist (γc ((j : ℝ) * l / n))
          (γc (((j + 1 : ℕ) : ℝ) * l / n)) ≤ l / n := by
        rw [carnot_dist_eq G hq hqpos hspan]
        have H := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hsub _ _ ha hab hbl)
        rw [ENNReal.toReal_ofReal (sub_nonneg.mpr hab)] at H
        convert H using 1
        push_cast
        ring
      calc
        _ ≤ l / n := hdist
        _ ≤ 3 * dist x y / (2 * n) := by
          have H := div_le_div_of_nonneg_right hlength hnR.le
          convert H using 1
          ring
        _ ≤ (3 / 16 : ℝ) * Real.sqrt (t / n) := chain_step_le_sqrt ht hn hcount

/-- Horizontal near-geodesics give a short-link chain at any positive spatial
scale, with a quadratic ceiling count and including coincident endpoints. -/
theorem exists_carnot_short_chain {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N)
    (hqpos : 0 < q) (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (x y : CarnotPoint G hq hqpos hspan) {t a : ℝ} (ht : 0 < t) (ha : 0 < a) :
    ∃ (n : ℕ) (c : ℕ → CarnotPoint G hq hqpos hspan),
      n = max 1 ⌈64 * dist x y ^ 2 / (a ^ 2 * t)⌉₊ ∧ 0 < n ∧ c 0 = x ∧ c n = y ∧
      (n : ℝ) ≤ 1 + 64 * dist x y ^ 2 / (a ^ 2 * t) ∧
      ∀ j, j < n → dist (c j) (c (j + 1)) ≤
        (3 / 16 : ℝ) * (a * Real.sqrt (t / n)) := by
  let n := max 1 ⌈64 * dist x y ^ 2 / (a ^ 2 * t)⌉₊
  have hn : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (max_one_ceil_bounds _).1
  have htime : 0 < a ^ 2 * t := mul_pos (sq_pos_of_pos ha) ht
  obtain ⟨c, hx, hy, hlinks⟩ := exists_carnot_chain_of_count G hq hqpos hspan x y htime n hn
    (max_one_ceil_bounds _).2
  refine ⟨n, c, rfl, hn, hx, hy, max_one_ceil_le (by positivity), ?_⟩
  intro j hj
  have he : Real.sqrt (a ^ 2 * t / n) = a * Real.sqrt (t / n) := by
    rw [mul_div_assoc, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha.le]
  simpa only [he] using hlinks j hj

end HeatKernel.Gaussian
