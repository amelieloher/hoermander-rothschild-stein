-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.TentMoments
public import HeatKernel.Geometry.BallVolume
import Mathlib.Tactic

/-! # Exact tent masses from the homogeneous ball-volume law -/

@[expose] public section
open MeasureTheory Set RothschildStein
open scoped ENNReal
namespace HeatKernel.Sobolev

/-- A linear tent has mass equal to ball volume divided by dimension plus one. -/
theorem lintegral_tent_of_volume_scaling {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [SFinite μ] {d : α → ℝ} (hd : Measurable d)
    (hnonneg : ∀ x, 0 ≤ d x) {V : ℝ≥0∞} (Q : ℕ)
    (hvolume : ∀ s ∈ Ioo (0 : ℝ) 1, μ {x | d x < s} = ENNReal.ofReal (s ^ Q) * V) :
    (∫⁻ x, ENNReal.ofReal (max (1 - d x) 0) ∂μ) =
      ENNReal.ofReal (1 / ((Q : ℝ) + 1)) * V := by
  have h := lintegral_mul_eq_lintegral_layers (μ := μ) (g := fun _ => 1) (k := fun _ => 1) hd measurable_const measurable_const
    (fun x => (lintegral_indicator_layers_eq_tent (hnonneg x)).symm)
  simp only [mul_one, lintegral_const, Measure.restrict_apply_univ, one_mul] at h
  rw [h]
  calc
    _ = ∫⁻ s in Ioo (0 : ℝ) 1, ENNReal.ofReal (s ^ Q) * V :=
      setLIntegral_congr_fun measurableSet_Ioo hvolume
    _ = _ := by rw [lintegral_mul_const _ (by fun_prop), lintegral_unit_pow]

/-- A squared tent has the second beta-integral mass. -/
theorem lintegral_tent_sq_of_volume_scaling {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [SFinite μ] {d : α → ℝ} (hd : Measurable d)
    (hnonneg : ∀ x, 0 ≤ d x) {V : ℝ≥0∞} (Q : ℕ)
    (hvolume : ∀ s ∈ Ioo (0 : ℝ) 1, μ {x | d x < s} = ENNReal.ofReal (s ^ Q) * V) :
    (∫⁻ x, ENNReal.ofReal (max (1 - d x) 0 ^ 2) ∂μ) =
      ENNReal.ofReal (2 / (((Q : ℝ) + 1) * ((Q : ℝ) + 2))) * V := by
  have h := lintegral_mul_eq_lintegral_layers (μ := μ) (g := fun _ => 1) hd
    (by fun_prop : Measurable (fun s : ℝ => ENNReal.ofReal (2 * (1 - s))))
    measurable_const (fun x => (lintegral_weighted_layers_eq_tent_sq (hnonneg x)).symm)
  simp only [mul_one, lintegral_const, Measure.restrict_apply_univ, one_mul] at h
  rw [h]
  calc
    _ = ∫⁻ s in Ioo (0 : ℝ) 1, ENNReal.ofReal (2 * (1 - s) * s ^ Q) * V := by
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro s hs
      dsimp only
      rw [hvolume s hs, ← mul_assoc, ← ENNReal.ofReal_mul (by nlinarith [hs.2] : 0 ≤ 2 * (1 - s))]
    _ = _ := by rw [lintegral_mul_const _ (by fun_prop), lintegral_unit_tent_mul_pow]

/-- Normalized horizontal distance has the exact ball-volume distribution. -/
theorem volume_horizontalDistance_div_lt {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (x : Fin N → ℝ) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    volume {y | (horizontalL2Distance (G.horizontalFields hq) x y).toReal / r < s} =
      ENNReal.ofReal (s ^ G.homogeneousDimension) *
        volume (horizontalBall (G.horizontalFields hq) x r) := by
  have hfinite (y : Fin N → ℝ) : horizontalL2Distance (G.horizontalFields hq) x y ≠ ⊤ :=
    horizontalL2Distance_ne_top_of_bracketSpansOn hqpos _ (G.horizontalFields_contDiff hq) hspan x y
  have he : {y | (horizontalL2Distance (G.horizontalFields hq) x y).toReal / r < s} =
      horizontalBall (G.horizontalFields hq) x (s * r) := by
    ext y
    rw [mem_ofPred_eq, div_lt_iff₀ hr]
    change _ ↔ horizontalL2Distance (G.horizontalFields hq) x y < ENNReal.ofReal (s * r)
    rw [← ENNReal.toReal_lt_toReal (hfinite y) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (mul_pos hs hr).le]
  rw [he, volume_horizontalBall G hq hw x (mul_pos hs hr),
    volume_horizontalBall G hq hw x hr, mul_pow, ENNReal.ofReal_mul (by positivity), mul_assoc]

/-- The normalized horizontal distance is measurable in coordinates. -/
theorem measurable_horizontalDistance_div {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq)) (x : Fin N → ℝ) (r : ℝ) :
    Measurable (fun y => (horizontalL2Distance (G.horizontalFields hq) x y).toReal / r) :=
  (((continuous_homogeneous_horizontalL2Distance G hq hqpos hspan).comp
    (continuous_const.prodMk continuous_id)).measurable.ennreal_toReal).div_const r

/-- The linear horizontal distance tent has the exact normalized denominator. -/
theorem lintegral_horizontal_tent {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (x : Fin N → ℝ) {r : ℝ} (hr : 0 < r) :
    (∫⁻ y, ENNReal.ofReal (max (1 -
      (horizontalL2Distance (G.horizontalFields hq) x y).toReal / r) 0)) =
      ENNReal.ofReal (1 / ((G.homogeneousDimension : ℝ) + 1)) *
        volume (horizontalBall (G.horizontalFields hq) x r) := by
  exact lintegral_tent_of_volume_scaling (measurable_horizontalDistance_div G hq hqpos hspan x r)
    (fun y => div_nonneg ENNReal.toReal_nonneg hr.le) _
    (fun s hs => volume_horizontalDistance_div_lt G hq hqpos hspan hw x hr hs.1)

/-- The squared horizontal distance tent has the exact normalized denominator. -/
theorem lintegral_horizontal_tent_sq {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (x : Fin N → ℝ) {r : ℝ} (hr : 0 < r) :
    (∫⁻ y, ENNReal.ofReal (max (1 -
      (horizontalL2Distance (G.horizontalFields hq) x y).toReal / r) 0 ^ 2)) =
      ENNReal.ofReal (2 / (((G.homogeneousDimension : ℝ) + 1) *
        ((G.homogeneousDimension : ℝ) + 2))) *
        volume (horizontalBall (G.horizontalFields hq) x r) := by
  exact lintegral_tent_sq_of_volume_scaling (measurable_horizontalDistance_div G hq hqpos hspan x r)
    (fun y => div_nonneg ENNReal.toReal_nonneg hr.le) _
    (fun s hs => volume_horizontalDistance_div_lt G hq hqpos hspan hw x hr hs.1)

/-- The ordinary integral denominator of the linear horizontal tent. -/
theorem integral_horizontal_tent {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (x : Fin N → ℝ) {r : ℝ} (hr : 0 < r) :
    (∫ y, max (1 - (horizontalL2Distance (G.horizontalFields hq) x y).toReal / r) 0) =
      volume.real (horizontalBall (G.horizontalFields hq) x r) /
        ((G.homogeneousDimension : ℝ) + 1) := by
  have hd := measurable_horizontalDistance_div G hq hqpos hspan x r
  have hm : Measurable (fun y => max (1 -
      (horizontalL2Distance (G.horizontalFields hq) x y).toReal / r) 0) :=
    (measurable_const.sub hd).max measurable_const
  rw [integral_eq_lintegral_of_nonneg_ae (f := fun y => max (1 -
      (horizontalL2Distance (G.horizontalFields hq) x y).toReal / r) 0)
    (Filter.Eventually.of_forall (fun y => le_max_right _ _)) hm.aestronglyMeasurable,
    lintegral_horizontal_tent G hq hqpos hspan hw x hr,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  simp only [Measure.real, div_eq_mul_inv, one_mul, mul_comm]

/-- The ordinary integral denominator of the squared horizontal tent. -/
theorem integral_horizontal_tent_sq {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (x : Fin N → ℝ) {r : ℝ} (hr : 0 < r) :
    (∫ y, max (1 - (horizontalL2Distance (G.horizontalFields hq) x y).toReal / r) 0 ^ 2) =
      2 * volume.real (horizontalBall (G.horizontalFields hq) x r) /
        (((G.homogeneousDimension : ℝ) + 1) * ((G.homogeneousDimension : ℝ) + 2)) := by
  have hd := measurable_horizontalDistance_div G hq hqpos hspan x r
  have hm : Measurable (fun y => max (1 -
      (horizontalL2Distance (G.horizontalFields hq) x y).toReal / r) 0) :=
    (measurable_const.sub hd).max measurable_const
  rw [integral_eq_lintegral_of_nonneg_ae (f := fun y => max (1 -
      (horizontalL2Distance (G.horizontalFields hq) x y).toReal / r) 0 ^ 2)
    (Filter.Eventually.of_forall (fun y => sq_nonneg _)) (hm.pow_const 2).aestronglyMeasurable,
    lintegral_horizontal_tent_sq G hq hqpos hspan hw x hr,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  simp only [Measure.real, div_eq_mul_inv]
  ring

/-- The linear horizontal tent has strictly positive mass. -/
theorem integral_horizontal_tent_pos {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (x : Fin N → ℝ) {r : ℝ} (hr : 0 < r) :
    0 < ∫ y, max (1 - (horizontalL2Distance (G.horizontalFields hq) x y).toReal / r) 0 := by
  rw [integral_horizontal_tent G hq hqpos hspan hw x hr]
  exact div_pos (ENNReal.toReal_pos (volume_horizontalBall_pos G hq hqpos hspan x hr).ne'
    (volume_horizontalBall_lt_top G hq hqpos hspan hw x hr.le).ne) (by positivity)

/-- The squared horizontal tent has strictly positive mass. -/
theorem integral_horizontal_tent_sq_pos {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (x : Fin N → ℝ) {r : ℝ} (hr : 0 < r) :
    0 < ∫ y, max (1 - (horizontalL2Distance (G.horizontalFields hq) x y).toReal / r) 0 ^ 2 := by
  rw [integral_horizontal_tent_sq G hq hqpos hspan hw x hr]
  have hv := ENNReal.toReal_pos (volume_horizontalBall_pos G hq hqpos hspan x hr).ne'
    (volume_horizontalBall_lt_top G hq hqpos hspan hw x hr.le).ne
  exact div_pos (mul_pos (by norm_num) hv) (by positivity)

/-- Both horizontal tent weights are integrable against coordinate volume. -/
theorem integrable_horizontal_tent_and_sq {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (x : Fin N → ℝ) {r : ℝ} (hr : 0 < r) :
    Integrable (fun y => max (1 -
      (horizontalL2Distance (G.horizontalFields hq) x y).toReal / r) 0) volume ∧
    Integrable (fun y => max (1 -
      (horizontalL2Distance (G.horizontalFields hq) x y).toReal / r) 0 ^ 2) volume := by
  have hd := measurable_horizontalDistance_div G hq hqpos hspan x r
  have hv := (volume_horizontalBall_lt_top G hq hqpos hspan hw x hr.le).ne
  have hm : Measurable (fun y => max (1 -
      (horizontalL2Distance (G.horizontalFields hq) x y).toReal / r) 0) :=
    (measurable_const.sub hd).max measurable_const
  constructor
  · apply (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun y => le_max_right _ _))).mp
    rw [lintegral_horizontal_tent G hq hqpos hspan hw x hr]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hv
  · apply (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable (hm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun y => sq_nonneg _))).mp
    rw [lintegral_horizontal_tent_sq G hq hqpos hspan hw x hr]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hv

end HeatKernel.Sobolev
