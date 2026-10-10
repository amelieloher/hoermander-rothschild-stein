-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.BoundedNonlinearEnergyEndpoints

/-! # Bounded extensions of square integrable curves

A finite essential spatial norm bound gives a real norm bound. Zero extension preserves
this bound and square integrability, supplying global curves for time averaging.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace HeatKernel

/-- A finite essential L² bound on an L²-valued curve gives an almost-everywhere norm bound. -/
theorem exists_ae_norm_le_of_essSup_eLpNorm_lt_top {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
    (v : β → Lp ℝ 2 μ)
    (hb : essSup (fun t => eLpNorm (v t) 2 μ) ν < ⊤) :
    ∃ M : ℝ≥0, ∀ᵐ t ∂ν, ‖v t‖ ≤ M := by
  let B := essSup (fun t => eLpNorm (v t) 2 μ) ν
  refine ⟨B.toNNReal, ?_⟩
  filter_upwards [ENNReal.ae_le_essSup (μ := ν) (fun t => eLpNorm (v t) 2 μ)] with t ht
  rw [Lp.norm_def]
  exact ENNReal.toReal_mono hb.ne ht

end HeatKernel
