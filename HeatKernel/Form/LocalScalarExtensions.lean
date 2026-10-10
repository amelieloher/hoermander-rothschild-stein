-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Tactic.Linter

/-! # Compactly supported extensions of local C¹ scalar maps -/

@[expose] public section

noncomputable section

open Set Filter TopologicalSpace Metric
open scoped NNReal Topology

namespace HeatKernel

/-- Every scalar map that is C¹ near a point agrees near that point with a global compactly
supported C¹ map with bounded derivative. -/
theorem exists_contDiff_compactSupport_extension_at {η : ℝ → ℝ} {x : ℝ}
    (hη : ContDiffAt ℝ 1 η x) :
    ∃ ψ : ℝ → ℝ, ∃ C : ℝ≥0, ContDiff ℝ 1 ψ ∧ HasCompactSupport ψ ∧
      (∀ s, ‖deriv ψ s‖ ≤ C) ∧ ψ =ᶠ[𝓝 x] η := by
  obtain ⟨V, hV, hxV, hηV⟩ := hη.contDiffOn' (m := 1) le_rfl (by simp)
  have hηV' : ContDiffOn ℝ 1 η V := by simpa using hηV
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hxV)
  let φ : ContDiffBump x :=
    { rIn := r / 4
      rOut := r / 2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  have hsupp : tsupport φ ⊆ V := by
    rw [φ.tsupport_eq]
    exact (closedBall_subset_ball (by dsimp [φ]; linarith)).trans hball
  let ψ : ℝ → ℝ := fun s => φ s * η s
  have hψ : ContDiff ℝ 1 ψ := by
    apply contDiff_iff_contDiffAt.mpr
    intro s
    by_cases hs : s ∈ tsupport φ
    · exact φ.contDiff.contDiffAt.mul (hηV'.contDiffAt (hV.mem_nhds (hsupp hs)))
    · have he : φ =ᶠ[𝓝 s] 0 := notMem_tsupport_iff_eventuallyEq.mp hs
      apply contDiffAt_const.congr_of_eventuallyEq
      filter_upwards [he] with t ht
      simpa only [Pi.zero_apply, zero_mul] using congrArg (fun z => z * η t) ht
  have hc : HasCompactSupport ψ := φ.hasCompactSupport.mul_right
  obtain ⟨C, hC⟩ := hψ.continuous_deriv_one.bounded_above_of_compact_support hc.deriv
  refine ⟨ψ, ⟨max 0 C, le_max_left _ _⟩, hψ, hc,
    fun s => (hC s).trans (le_max_right _ _), ?_⟩
  filter_upwards [φ.eventuallyEq_one] with s hs
  change φ s * η s = η s
  simpa only [Pi.one_apply, one_mul] using congrArg (fun z => z * η s) hs



end HeatKernel
