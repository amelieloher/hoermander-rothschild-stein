-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Tactic

/-!
# Positive averaging kernels and overlapping covers

The kernel estimates use column mass at most one and a uniform bound on the
kernel. The covering estimate isolates the local oscillation and overlap inputs
needed to pass from a Poincaré inequality to a global averaging error bound.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

namespace HeatKernel.Sobolev

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- A positive integral kernel with column mass at most one does not increase the L¹ integral. -/
theorem lintegral_averageKernel_le [SFinite μ] {k : α → α → ℝ≥0∞} {f : α → ℝ≥0∞}
    (hk : Measurable (Function.uncurry k)) (hf : Measurable f)
    (hcol : ∀ y, ∫⁻ x, k x y ∂μ ≤ 1) :
    (∫⁻ x, ∫⁻ y, k x y * f y ∂μ ∂μ) ≤ ∫⁻ y, f y ∂μ := by
  rw [lintegral_lintegral_swap (by fun_prop)]
  apply lintegral_mono
  intro y
  dsimp only
  rw [lintegral_mul_const _ (hk.of_uncurry_right)]
  simpa only [one_mul] using mul_le_mul' (hcol y) (le_refl (f y))

/-- The uniform kernel bound gives a pointwise L¹-to-L∞ estimate. -/
theorem averageKernel_le_mul_lintegral {k : α → α → ℝ≥0∞} {f : α → ℝ≥0∞}
    (hf : Measurable f) {c : ℝ≥0∞} (hkernel : ∀ x y, k x y ≤ c) (x : α) :
    (∫⁻ y, k x y * f y ∂μ) ≤ c * ∫⁻ y, f y ∂μ := by
  rw [← lintegral_const_mul c hf]
  exact lintegral_mono (fun y => mul_le_mul' (hkernel x y) le_rfl)

/-- Combining the L¹ and L∞ estimates gives the squared L² estimate. -/
theorem lintegral_averageKernel_sq_le [SFinite μ]
    {k : α → α → ℝ≥0∞} {f : α → ℝ≥0∞}
    (hk : Measurable (Function.uncurry k)) (hf : Measurable f)
    (hcol : ∀ y, ∫⁻ x, k x y ∂μ ≤ 1)
    {c : ℝ≥0∞} (hkernel : ∀ x y, k x y ≤ c) :
    (∫⁻ x, (∫⁻ y, k x y * f y ∂μ) ^ 2 ∂μ) ≤ c * (∫⁻ y, f y ∂μ) ^ 2 := by
  have hm : Measurable (fun x => ∫⁻ y, k x y * f y ∂μ) :=
    (by fun_prop : Measurable (fun z : α × α => k z.1 z.2 * f z.2)).lintegral_prod_right'
  calc
    _ ≤ ∫⁻ x, (c * ∫⁻ y, f y ∂μ) * (∫⁻ y, k x y * f y ∂μ) ∂μ := by
      apply lintegral_mono
      intro x
      dsimp only
      rw [pow_two]
      exact mul_le_mul' (averageKernel_le_mul_lintegral hf hkernel x) le_rfl
    _ = (c * ∫⁻ y, f y ∂μ) * (∫⁻ x, ∫⁻ y, k x y * f y ∂μ ∂μ) :=
      lintegral_const_mul _ hm
    _ ≤ (c * ∫⁻ y, f y ∂μ) * (∫⁻ y, f y ∂μ) :=
      mul_le_mul' le_rfl (lintegral_averageKernel_le hk hf hcol)
    _ = c * (∫⁻ y, f y ∂μ) ^ 2 := by ring

/-- A measurable cover with bounded overlap sums local energy bounds globally. -/
theorem lintegral_le_of_cover_local_energy {ι : Type*} [Countable ι]
    {U W : ι → Set α} (hcover : ⋃ i, U i = univ)
    (hW : ∀ i, MeasurableSet (W i)) {e g : α → ℝ≥0∞} (hg : Measurable g)
    {C N : ℝ≥0∞}
    (hlocal : ∀ i, (∫⁻ x in U i, e x ∂μ) ≤ C * ∫⁻ x in W i, g x ∂μ)
    (hoverlap : ∀ x, ∑' i, (W i).indicator (fun _ => (1 : ℝ≥0∞)) x ≤ N) :
    (∫⁻ x, e x ∂μ) ≤ C * N * ∫⁻ x, g x ∂μ := by
  calc
    _ = ∫⁻ x in ⋃ i, U i, e x ∂μ := by rw [hcover, Measure.restrict_univ]
    _ ≤ ∑' i, ∫⁻ x in U i, e x ∂μ := lintegral_iUnion_le U e
    _ ≤ ∑' i, C * ∫⁻ x in W i, g x ∂μ := ENNReal.tsum_le_tsum hlocal
    _ = C * ∑' i, ∫⁻ x in W i, g x ∂μ := ENNReal.tsum_mul_left
    _ = C * ∫⁻ x, ∑' i, (W i).indicator g x ∂μ := by
      congr 1
      simp_rw [← lintegral_indicator (hW _)]
      rw [lintegral_tsum (fun i => (hg.indicator (hW i)).aemeasurable)]
    _ ≤ C * ∫⁻ x, N * g x ∂μ := by
      gcongr with x
      have heq : (∑' i, (W i).indicator g x) =
          (∑' i, (W i).indicator (fun _ => (1 : ℝ≥0∞)) x) * g x := by
        rw [← ENNReal.tsum_mul_right]
        congr 1
        funext i
        by_cases hx : x ∈ W i <;> simp [hx]
      rw [heq]
      exact mul_le_mul' (hoverlap x) le_rfl
    _ = C * N * ∫⁻ x, g x ∂μ := by rw [lintegral_const_mul N hg, mul_assoc]

end HeatKernel.Sobolev
