-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-! # Local integrability from square integrability or boundedness

On measures finite on compact sets, square integrability on compact subsets implies local
integrability. The same holds for measurable functions bounded on every compact subset.
-/

@[expose] public section

noncomputable section

namespace HeatKernel

open MeasureTheory Set Filter
open scoped ENNReal

variable {E : Type*} [MeasureSpace E] {μ : Measure E}

variable [TopologicalSpace E] [LocallyCompactSpace E] [IsFiniteMeasureOnCompacts μ]

/-- Square integrability on each compact subset of an open set implies local integrability. -/
theorem locallyIntegrableOn_of_memLp_two_on_compacts {s : Set E} (hs : IsOpen s)
    {f : E → ℝ} (hf : ∀ K ⊆ s, IsCompact K → MemLp f 2 (μ.restrict K)) :
    LocallyIntegrableOn f s μ := by
  rw [locallyIntegrableOn_iff hs.isLocallyClosed]
  intro K hKs hK
  have : IsFiniteMeasure (μ.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
  exact MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) (hf K hKs hK)

variable [T2Space E] [OpensMeasurableSpace E]

/-- A measurable function bounded on each compact subset of an open set is locally integrable. -/
theorem locallyIntegrableOn_of_bounded_on_compacts {s : Set E} (hs : IsOpen s)
    {f : E → ℝ} (hf : AEStronglyMeasurable f (μ.restrict s))
    (hbound : ∀ K ⊆ s, IsCompact K → ∃ C : ℝ, ∀ x ∈ K, ‖f x‖ ≤ C) :
    LocallyIntegrableOn f s μ := by
  rw [locallyIntegrableOn_iff hs.isLocallyClosed]
  intro K hKs hK
  obtain ⟨C, hC⟩ := hbound K hKs hK
  refine IntegrableOn.of_bound hK.measure_lt_top
    (hf.mono_measure (Measure.restrict_mono hKs le_rfl)) C ?_
  exact (ae_restrict_mem₀ hK.nullMeasurableSet).mono fun x hx => hC x hx

end HeatKernel
