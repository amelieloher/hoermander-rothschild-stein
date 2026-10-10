-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Geometry.CarnotPoint
public import RothschildStein.G2.Measure
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Measure.OpenPos

/-! Exact horizontal ball volumes from Haar invariance and homogeneous dilation. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory RothschildStein Filter
open scoped ENNReal Topology
namespace HeatKernel

/-- Horizontal balls are open in coordinates. -/
theorem isOpen_horizontalBall {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N)
    (hqpos : 0 < q) (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (x : Fin N → ℝ) (r : ℝ) : IsOpen (horizontalBall (G.horizontalFields hq) x r) :=
  isOpen_lt ((continuous_homogeneous_horizontalL2Distance G hq hqpos hspan).comp
    (continuous_const.prodMk continuous_id)) continuous_const

/-- Every positive-radius horizontal ball has positive volume. -/
theorem volume_horizontalBall_pos {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N)
    (hqpos : 0 < q) (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (x : Fin N → ℝ) {r : ℝ} (hr : 0 < r) :
    0 < volume (horizontalBall (G.horizontalFields hq) x r) := by
  apply (isOpen_horizontalBall G hq hqpos hspan x r).measure_pos volume
  exact ⟨x, by simpa only [horizontalBall, mem_ofPred_eq, horizontalL2Distance_self] using
    ENNReal.ofReal_pos.mpr hr⟩

/-- Finite-radius horizontal balls have finite volume. -/
theorem volume_horizontalBall_lt_top {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N)
    (hqpos : 0 < q) (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (x : Fin N → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    volume (horizontalBall (G.horizontalFields hq) x r) < ⊤ := by
  have hsub : horizontalBall (G.horizontalFields hq) x r ⊆
      {y | horizontalL2Distance (G.horizontalFields hq) x y ≤ ENNReal.ofReal r} :=
    fun y hy => (show horizontalL2Distance (G.horizontalFields hq) x y < ENNReal.ofReal r from hy).le
  exact (measure_mono hsub).trans_lt
    (isCompact_horizontal_closedBall G hq hqpos hspan hw x hr).measure_lt_top

/-- Left translation preserves the volume of any set of coordinates. -/
theorem volume_leftTranslation_image {N : ℕ} (G : HomogeneousGroup N)
    (x : Fin N → ℝ) (s : Set (Fin N → ℝ)) : volume (G.mul x '' s) = volume s := by
  have he := (G2.measurePreserving_leftTranslation G x).measurable.measurableEmbedding
    (G2.leftTranslation_bijective G x).injective
  have hm := (G2.measurePreserving_leftTranslation G x).measure_preimage_emb he (G.mul x '' s)
  simpa only [preimage_image_eq _ he.injective] using hm.symm

/-- Open ball volume is exactly the unit-ball volume times the radius to homogeneous dimension. -/
theorem volume_horizontalBall {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (x : Fin N → ℝ) {r : ℝ} (hr : 0 < r) :
    volume (horizontalBall (G.horizontalFields hq) x r) =
      ENNReal.ofReal (r ^ G.homogeneousDimension) *
        volume (horizontalBall (G.horizontalFields hq) 0 1) := by
  rw [horizontalBall_eq_image_unitBall G hq hw hr, ← image_image,
    volume_leftTranslation_image, G2.volume_dilate_image G hr]

/-- Doubling for open horizontal balls has the exact factor two to homogeneous dimension. -/
theorem volume_horizontalBall_double {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (x : Fin N → ℝ) {r : ℝ} (hr : 0 < r) :
    volume (horizontalBall (G.horizontalFields hq) x (2 * r)) =
      (2 : ℝ≥0∞) ^ G.homogeneousDimension * volume (horizontalBall (G.horizontalFields hq) x r) := by
  rw [volume_horizontalBall G hq hw x (by linarith), volume_horizontalBall G hq hw x hr,
    mul_pow, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
  norm_num only [ENNReal.ofReal_ofNat]
  exact _root_.mul_assoc _ _ _

end HeatKernel
