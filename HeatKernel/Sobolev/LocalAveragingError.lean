-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.AveragingKernel
import Mathlib.Tactic

/-!
# Local oscillations control the averaging error

Each averaging kernel is supported in the larger ball and bounded by the
reciprocal volume of the smaller ball. The pointwise quadratic estimate and
same-ball Poincaré inequality then sum over a cover of bounded overlap.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace HeatKernel.Sobolev

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- A localized averaging error is at most four times the larger-ball oscillation. -/
theorem lintegral_local_average_error_le
    {U W : Set α} (hW : MeasurableSet W) {e h : α → ℝ≥0∞} (hh : Measurable h)
    {k : α → α → ℝ≥0∞} {c : ℝ≥0∞}
    (hkernel : ∀ x ∈ U, ∀ y, k x y ≤ c)
    (hsupport : ∀ x ∈ U, ∀ y ∉ W, k x y = 0)
    (hvolume : c * μ U ≤ 1) (hsubset : U ⊆ W)
    (hpoint : ∀ x ∈ U, e x ≤ 2 * h x + 2 * ∫⁻ y, k x y * h y ∂μ) :
    (∫⁻ x in U, e x ∂μ) ≤ 4 * ∫⁻ x in W, h x ∂μ := by
  have haverage (x : α) (hx : x ∈ U) :
      (∫⁻ y, k x y * h y ∂μ) ≤ c * ∫⁻ y in W, h y ∂μ := by
    rw [← lintegral_indicator hW, ← lintegral_const_mul c (hh.indicator hW)]
    apply lintegral_mono
    intro y
    by_cases hy : y ∈ W
    · simpa only [indicator_of_mem hy] using mul_le_mul' (hkernel x hx y) (le_refl (h y))
    · simp [hsupport x hx y hy, hy]
  have hp (x : α) (hx : x ∈ U) :
      e x ≤ 2 * h x + 2 * c * ∫⁻ y in W, h y ∂μ := by
    exact (hpoint x hx).trans (add_le_add le_rfl
      (by simpa only [mul_assoc] using mul_le_mul' (le_refl (2 : ℝ≥0∞)) (haverage x hx)))
  calc
    _ ≤ ∫⁻ x in U, (2 * h x + 2 * c * ∫⁻ y in W, h y ∂μ) ∂μ :=
      setLIntegral_mono (by fun_prop) hp
    _ = 2 * (∫⁻ x in U, h x ∂μ) +
        (2 * c * ∫⁻ y in W, h y ∂μ) * μ U := by
      rw [lintegral_add_left (f := fun x => 2 * h x) (by fun_prop) _,
        lintegral_const_mul 2 hh, lintegral_const, Measure.restrict_apply_univ]
    _ ≤ 2 * (∫⁻ x in W, h x ∂μ) + 2 * (∫⁻ y in W, h y ∂μ) := by
      apply add_le_add
      · exact mul_le_mul' le_rfl (lintegral_mono_set hsubset)
      · calc
          _ = 2 * (∫⁻ y in W, h y ∂μ) * (c * μ U) := by ring
          _ ≤ 2 * (∫⁻ y in W, h y ∂μ) * 1 := mul_le_mul' le_rfl hvolume
          _ = _ := mul_one _
    _ = _ := by ring

end HeatKernel.Sobolev
