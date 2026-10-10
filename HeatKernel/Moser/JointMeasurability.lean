-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib

/-!
# Measurable limits and coefficient fluxes

Selection of strongly measurable representatives from almost everywhere convergent
approximations, and preservation of square integrability by bounded matrix coefficients.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology BigOperators ENNReal

namespace HeatKernel

/-- A bounded measurable scalar coefficient preserves square integrability. -/
theorem memLp_two_mul_of_ae_bound {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {a g : α → ℝ} {C : ℝ}
    (ha : AEStronglyMeasurable a μ) (hg : MemLp g 2 μ)
    (hbound : ∀ᵐ x ∂μ, ‖a x‖ ≤ C) : MemLp (fun x => a x * g x) 2 μ := by
  apply hg.of_le_mul (c := C) (ha.mul hg.aestronglyMeasurable)
  filter_upwards [hbound] with x hx
  change ‖a x * g x‖ ≤ C * ‖g x‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg (g x))

/-- Each component of a bounded measurable matrix flux is square integrable. -/
theorem memLp_two_matrix_flux {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    {μ : Measure α} {a : ι → ι → α → ℝ} {g : ι → α → ℝ} {C : ℝ}
    (ha : ∀ i j, AEStronglyMeasurable (a i j) μ)
    (hg : ∀ j, MemLp (g j) 2 μ)
    (hbound : ∀ i j, ∀ᵐ x ∂μ, ‖a i j x‖ ≤ C) (i : ι) :
    MemLp (fun x => ∑ j, a i j x * g j x) 2 μ := by
  exact memLp_finsetSum _ fun j _ =>
    memLp_two_mul_of_ae_bound (ha i j) (hg j) (hbound i j)

end HeatKernel
