-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.CountableEvaluations
public import HeatKernel.Kernel.LocalIntegrability
public import HeatKernel.Kernel.CompactTestIntegrability

/-! # Local integrability of the representative kernel

Scalar continuity of the semigroup representatives gives joint measurability
and uniform bounds on positive-time compact sets, hence local integrability.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace HeatKernel

/-- The representative kernel is locally integrable on positive product spacetime. -/
theorem locallyIntegrableOn_heatRepresentativeKernel {n : ℕ}
    (T : ℝ → Lp ℝ 2 (volume : Measure (Fin n → ℝ)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (Fin n → ℝ)))
    (u : ℝ → Lp ℝ 2 (volume : Measure (Fin n → ℝ)) → (Fin n → ℝ) → ℝ)
    (hu : ∀ t, 0 < t → ∀ f, Continuous (u t f))
    (hae : ∀ t, 0 < t → ∀ f, T t f =ᵐ[volume] u t f)
    (hjoint : ∀ f, ContinuousOn (fun p : ℝ × (Fin n → ℝ) => u p.1 f p.2)
      {p | 0 < p.1}) :
    LocallyIntegrableOn (fun p : ℝ × ((Fin n → ℝ) × (Fin n → ℝ)) =>
      evaluationKernel (heatRepresentativeEvaluation T u hu hae) p.1 p.2.1 p.2.2)
      {p | 0 < p.1} volume := by
  apply locallyIntegrableOn_of_bounded_on_compacts (isOpen_lt continuous_const continuous_fst)
    (measurable_heatRepresentativeKernel T u hu hae hjoint).aestronglyMeasurable.restrict
  intro K hKpos hK
  obtain ⟨C, _hC, hbound⟩ := exists_abs_heatRepresentativeKernel_bound_on_compact
    T u hu hae hjoint hK (fun p hp => hKpos hp)
  exact ⟨C, by simpa only [Real.norm_eq_abs] using hbound⟩

end HeatKernel
