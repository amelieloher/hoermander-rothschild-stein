-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.LocalAveragingError
import Mathlib.Tactic

/-! # Averaging error from Poincaré estimates on larger energy sets -/

@[expose] public section
open Set MeasureTheory
open scoped ENNReal
namespace HeatKernel.Sobolev

/-- Local oscillation estimates may use larger energy sets with their own overlap bound. -/
theorem lintegral_average_error_le_of_enlarged_poincare
    {α ι : Type*} [MeasurableSpace α] [Countable ι] {μ : Measure α}
    {U W Z : ι → Set α} (hcover : ⋃ i, U i = univ)
    (hW : ∀ i, MeasurableSet (W i)) (hZ : ∀ i, MeasurableSet (Z i))
    (hsubset : ∀ i, U i ⊆ W i) {e g : α → ℝ≥0∞} (hg : Measurable g)
    {h : ι → α → ℝ≥0∞} (hh : ∀ i, Measurable (h i))
    {k : α → α → ℝ≥0∞} {c P s K : ℝ≥0∞}
    (hkernel : ∀ i, ∀ x ∈ U i, ∀ y, k x y ≤ c)
    (hsupport : ∀ i, ∀ x ∈ U i, ∀ y ∉ W i, k x y = 0)
    (hvolume : ∀ i, c * μ (U i) ≤ 1)
    (hpoint : ∀ i, ∀ x ∈ U i, e x ≤ 2 * h i x + 2 * ∫⁻ y, k x y * h i y ∂μ)
    (hpoincare : ∀ i, (∫⁻ x in W i, h i x ∂μ) ≤ P * s ^ 2 * ∫⁻ x in Z i, g x ∂μ)
    (hoverlap : ∀ x, ∑' i, (Z i).indicator (fun _ => (1 : ℝ≥0∞)) x ≤ K) :
    (∫⁻ x, e x ∂μ) ≤ (4 * P * s ^ 2) * K * ∫⁻ x, g x ∂μ := by
  apply lintegral_le_of_cover_local_energy hcover hZ hg _ hoverlap
  intro i
  have H := lintegral_local_average_error_le (hW i) (hh i) (hkernel i)
    (hsupport i) (hvolume i) (hsubset i) (hpoint i)
  apply H.trans
  simpa only [mul_assoc] using mul_le_mul' (le_refl (4 : ℝ≥0∞)) (hpoincare i)

end HeatKernel.Sobolev
