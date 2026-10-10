-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # Integrable products with compact tests

Local integrability on a domain suffices for multiplication by a continuous
compact test whose support is contained in that domain.
-/

@[expose] public section

noncomputable section

open MeasureTheory TopologicalSpace

namespace HeatKernel

/-- A locally integrable function times a compact continuous test is globally integrable. -/
theorem integrable_mul_compact_test_of_locallyIntegrableOn {E : Type*}
    [MeasurableSpace E] [TopologicalSpace E] [T2Space E] [OpensMeasurableSpace E]
    {μ : Measure E} {Ω : Set E} {f ψ : E → ℝ}
    (hf : LocallyIntegrableOn f Ω μ) (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ Ω) :
    Integrable (fun x => f x * ψ x) μ := by
  apply (integrableOn_iff_integrable_of_support_subset (s := tsupport ψ) ?_).mp
  · exact (hf.integrableOn_compact_subset hs hc).mul_continuousOn hψ.continuousOn hc
  · intro x hx
    by_contra hnot
    exact hx (by simp only [image_eq_zero_of_notMem_tsupport hnot, mul_zero])

end HeatKernel
