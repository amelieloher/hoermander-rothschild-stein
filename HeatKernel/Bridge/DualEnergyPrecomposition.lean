-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Bridge.DualEnergyPair
public import HeatKernel.Bridge.DualTimePrecomposition
import Mathlib.Tactic.Linter

/-! # Continuous changes of tests in dual energy pairs -/

@[expose] public section
open Set MeasureTheory
namespace HeatKernel

/-- A bounded linear change of tests preserves both L² dual representatives,
their specified evaluations, and their weak time balance. -/
theorem IsDualEnergyPair.precompose {E H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {J : Set ℝ} {value flux : ℝ → E → ℝ} {D F : ℝ → (E →L[ℝ] ℝ)}
    (h : IsDualEnergyPair J value flux D F) (A : H →L[ℝ] E) :
    IsDualEnergyPair J (fun t v => value t (A v)) (fun t v => flux t (A v))
      (fun t => dualPrecomposition A (D t)) (fun t => dualPrecomposition A (F t)) := by
  obtain ⟨hD, hF, hDr, hFr, ht⟩ := h
  refine ⟨memLp_dualPrecomposition A hD, memLp_dualPrecomposition A hF,
    ?_, ?_, ht.precompose A⟩
  · filter_upwards [hDr] with t ht
    intro v
    exact ht (A v)
  · filter_upwards [hFr] with t ht
    intro v
    exact ht (A v)

end HeatKernel
