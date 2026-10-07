-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.P1
variable {N : ℕ} {μ : Measure (Fin N → ℝ)}
  {U A : Set (Fin N → ℝ)} {f : (Fin N → ℝ) → ℝ}

/-- Localize an ambient truncation to a measurable
chart on which its integrand is supported. No measurability of A is needed. -/
theorem integrableOn_localizedTruncation_iff (hU : MeasurableSet U)
    (hz : ∀ x, x ∉ U → f x = 0) :
    IntegrableOn f (A ∩ U) μ ↔ IntegrableOn f A μ := by
  refine ⟨fun hi => ?_, fun hi => hi.mono_set inter_subset_left⟩
  have hlocal : IntegrableOn f U (μ.restrict A) := by
    change Integrable f ((μ.restrict A).restrict U)
    rw [Measure.restrict_restrict hU, inter_comm]
    exact hi
  exact hlocal.integrable_of_forall_notMem_eq_zero hz

/-- Ambient and localized truncated integrals agree
when the integrand vanishes off the chart, for arbitrary truncation sets. -/
theorem integral_localizedTruncation (hU : MeasurableSet U)
    (hz : ∀ x, x ∉ U → f x = 0) :
    (∫ x in A ∩ U, f x ∂μ) = ∫ x in A, f x ∂μ := by
  calc
    _ = ∫ x in U, f x ∂μ.restrict A := by
      rw [Measure.restrict_restrict hU, inter_comm]
    _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero hz

end RothschildStein.P1
