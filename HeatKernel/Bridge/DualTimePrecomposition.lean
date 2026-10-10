-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Bridge.DualTimeBalance
import Mathlib.Tactic.Linter

/-! # Continuous changes of form tests in weak time balances -/

@[expose] public section
open Set MeasureTheory
namespace HeatKernel

/-- A bounded linear change of form tests preserves the Bochner weak time
balance and all its scalar evaluations. -/
theorem SatisfiesDualTimeBalance.precompose {E H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {J : Set ℝ} {D F : ℝ → (E →L[ℝ] ℝ)} (h : SatisfiesDualTimeBalance J D F)
    (A : H →L[ℝ] E) :
    SatisfiesDualTimeBalance J (fun t => dualPrecomposition A (D t))
      (fun t => dualPrecomposition A (F t)) := by
  intro ψ hψ hcψ hsψ
  obtain ⟨hiD, hiF, _, hv⟩ := h ψ hψ hcψ hsψ
  have hd : Integrable (fun t => deriv ψ t • dualPrecomposition A (D t))
      (volume.restrict J) := by
    simpa only [map_smul] using (dualPrecomposition A).integrable_comp hiD
  have hf : Integrable (fun t => ψ t • dualPrecomposition A (F t))
      (volume.restrict J) := by
    simpa only [map_smul] using (dualPrecomposition A).integrable_comp hiF
  refine ⟨hd, hf, integral_smul_dual_eq_of_eval hd hf ?_, ?_⟩
  · intro v
    simpa only [dualPrecomposition_apply] using (hv (A v)).2.2
  · intro v
    simpa only [dualPrecomposition_apply] using hv (A v)

end HeatKernel
