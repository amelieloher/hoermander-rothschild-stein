-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.JointMeasurability
public import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic.Linter

/-! # Compact continuous time multipliers on square-integrable space-time data -/

@[expose] public section
open MeasureTheory
namespace HeatKernel

/-- A compact continuous temporal multiplier preserves space-time square integrability. -/
theorem memLp_two_mul_time_of_compact_support {α : Type*} [MeasurableSpace α]
    {μ : Measure (ℝ × α)} {f : ℝ × α → ℝ} (hf : MemLp f 2 μ)
    {ψ : ℝ → ℝ} (hψ : Continuous ψ) (hc : HasCompactSupport ψ) :
    MemLp (fun z => ψ z.1 * f z) 2 μ := by
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hψ
  apply memLp_two_mul_of_ae_bound (hψ.measurable.comp measurable_fst).aestronglyMeasurable hf
  exact Filter.Eventually.of_forall fun z => hC z.1

end HeatKernel
