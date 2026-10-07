-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.KernelClass

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory
variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

/-- The absent fractional piece satisfies the full kernel class with
zero size and smoothness constants and any permitted exponents (BB pp. 357–359). -/
theorem zeroKernel_class (μ : Measure X) {E : Set X} (hE : MeasurableSet E)
    {β ν : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (hν : 0 ≤ ν) :
    H2.KernelClass μ E β ν 0 0 (fun _ _ => 0) := by
  refine ⟨hE, measurable_const, hβ, hβ1, hν, le_rfl, le_rfl, ?_, ?_⟩
  · intro x hx y hy hxy
    simp
  · intro x₀ hx₀ x hx y hy hsep
    simp

end RothschildStein.H3
