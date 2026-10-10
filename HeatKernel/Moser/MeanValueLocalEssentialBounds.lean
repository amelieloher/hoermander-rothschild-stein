-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.OuterMeasure.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.Compactness.Compact
import Mathlib.Tactic

/-! # Essential bounds from open local covers -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal
namespace HeatKernel

/-- A common essential bound on an open neighborhood of each point gives the
same essential bound on the whole open set in a second-countable space. -/
theorem eLpNormEssSup_restrict_le_of_local_bounds
    {α : Type*} [TopologicalSpace α] [SecondCountableTopology α]
    [MeasurableSpace α] [OpensMeasurableSpace α]
    (μ : Measure α) {U : Set α} (hU : IsOpen U)
    (f : α → ℝ) (K : ℝ≥0∞)
    (hlocal : ∀ x ∈ U, ∃ V : Set α, IsOpen V ∧ x ∈ V ∧
      eLpNormEssSup f (μ.restrict V) ≤ K) :
    eLpNormEssSup f (μ.restrict U) ≤ K := by
  let B := {x | x ∈ U ∧ ¬ ‖f x‖ₑ ≤ K}
  have hB : μ B = 0 := by
    apply measure_null_of_locally_null
    intro x hx
    obtain ⟨V, hV, hxV, hb⟩ := hlocal x hx.1
    have hae : ∀ᵐ y ∂μ.restrict V, ‖f y‖ₑ ≤ K :=
      ae_le_eLpNormEssSup.mono fun _ hy => hy.trans hb
    have hzero : μ {y | y ∈ V ∧ ¬ ‖f y‖ₑ ≤ K} = 0 := by
      rw [ae_restrict_iff' hV.measurableSet, ae_iff] at hae
      simpa only [not_imp] using hae
    refine ⟨V ∩ B, inter_mem
      (mem_nhdsWithin_of_mem_nhds (hV.mem_nhds hxV)) self_mem_nhdsWithin, ?_⟩
    have hs : V ∩ B ⊆ {y | y ∈ V ∧ ¬ ‖f y‖ₑ ≤ K} :=
      fun _ hy => ⟨hy.1, hy.2.2⟩
    exact measure_mono_null hs hzero
  apply eLpNormEssSup_le_of_ae_enorm_bound
  rw [ae_restrict_iff' hU.measurableSet, ae_iff]
  simpa only [B, not_imp] using hB

end HeatKernel
