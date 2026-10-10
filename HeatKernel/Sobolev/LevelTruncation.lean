-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

/-!
# Level truncations and their moments

The truncation is zero below a level and constant above twice that level.
Its first and second moments compare directly with the distribution function.
No differential or form-domain property is used in these measure estimates.
-/

@[expose] public section

open MeasureTheory Set

namespace HeatKernel.Sobolev

variable {α : Type*}

/-- The height-limited part of the absolute value above a positive level. -/
def levelTruncation (u : α → ℝ) (t : ℝ) (x : α) : ℝ :=
  min (max (|u x| - t) 0) t

/-- The truncation takes values between zero and its height. -/
theorem levelTruncation_bounds (u : α → ℝ) {t : ℝ} (ht : 0 ≤ t) (x : α) :
    0 ≤ levelTruncation u t x ∧ levelTruncation u t x ≤ t := by
  exact ⟨le_min (le_max_right _ _) ht, min_le_right _ _⟩

/-- Below its threshold the truncation vanishes. -/
theorem levelTruncation_eq_zero (u : α → ℝ) {t : ℝ} (ht : 0 ≤ t)
    {x : α} (hx : |u x| ≤ t) : levelTruncation u t x = 0 := by
  simp [levelTruncation, max_eq_right (sub_nonpos.mpr hx), ht]

/-- Above twice the threshold the truncation has full height. -/
theorem levelTruncation_eq_height (u : α → ℝ) {t : ℝ}
    {x : α} (hx : 2 * t ≤ |u x|) : levelTruncation u t x = t := by
  unfold levelTruncation
  apply min_eq_right
  exact (by linarith : t ≤ |u x| - t).trans (le_max_left _ _)

variable [MeasurableSpace α] {μ : Measure α}

/-- Measurability is preserved by the scalar truncation. -/
theorem measurable_levelTruncation {u : α → ℝ} (hu : Measurable u) (t : ℝ) :
    Measurable (levelTruncation u t) := by
  unfold levelTruncation
  fun_prop

/-- On a finite measure space the bounded truncation is integrable. -/
theorem integrable_levelTruncation [IsFiniteMeasure μ] {u : α → ℝ}
    (hu : Measurable u) {t : ℝ} (ht : 0 ≤ t) : Integrable (levelTruncation u t) μ := by
  apply Integrable.of_bound (measurable_levelTruncation hu t).aestronglyMeasurable t
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (levelTruncation_bounds u ht x).1]
    exact (levelTruncation_bounds u ht x).2)

/-- The quadratic moment of the truncation is finite. -/
theorem integrable_levelTruncation_sq [IsFiniteMeasure μ] {u : α → ℝ}
    (hu : Measurable u) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun x => levelTruncation u t x ^ 2) μ := by
  apply Integrable.of_bound ((measurable_levelTruncation hu t).pow_const 2).aestronglyMeasurable
    (t ^ 2)
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (levelTruncation_bounds u ht x).1
      (levelTruncation_bounds u ht x).2 2)

/-- The first moment is bounded by height times the measure of the lower superlevel set. -/
theorem integral_levelTruncation_le [IsFiniteMeasure μ] {u : α → ℝ}
    (hu : Measurable u) {t : ℝ} (ht : 0 ≤ t) :
    (∫ x, levelTruncation u t x ∂μ) ≤ t * μ.real {x | t < |u x|} := by
  have hs : MeasurableSet {x | t < |u x|} := by measurability
  calc
    _ ≤ ∫ x, {x | t < |u x|}.indicator (fun _ => t) x ∂μ := by
      apply integral_mono (integrable_levelTruncation hu ht)
        ((integrable_const t).indicator hs)
      intro x
      by_cases hx : t < |u x|
      · simpa [hx] using (levelTruncation_bounds u ht x).2
      · simp [hx, levelTruncation_eq_zero u ht (le_of_not_gt hx)]
    _ = t * μ.real {x | t < |u x|} := by
      rw [integral_indicator_const t hs, smul_eq_mul, mul_comm]

/-- The second moment dominates height squared times the upper superlevel measure. -/
theorem sq_mul_measure_le_integral_levelTruncation_sq [IsFiniteMeasure μ] {u : α → ℝ}
    (hu : Measurable u) {t : ℝ} (ht : 0 ≤ t) :
    t ^ 2 * μ.real {x | 2 * t < |u x|} ≤ ∫ x, levelTruncation u t x ^ 2 ∂μ := by
  have hs : MeasurableSet {x | 2 * t < |u x|} := by measurability
  calc
    _ = ∫ x, {x | 2 * t < |u x|}.indicator (fun _ => t ^ 2) x ∂μ := by
      rw [integral_indicator_const (t ^ 2) hs, smul_eq_mul, mul_comm]
    _ ≤ ∫ x, levelTruncation u t x ^ 2 ∂μ := by
      apply integral_mono ((integrable_const (t ^ 2)).indicator hs)
        (integrable_levelTruncation_sq hu ht)
      intro x
      by_cases hx : 2 * t < |u x|
      · simp [hx, levelTruncation_eq_height u hx.le]
      · simpa [hx] using sq_nonneg (levelTruncation u t x)

end HeatKernel.Sobolev
