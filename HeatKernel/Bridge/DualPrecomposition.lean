-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Tactic.Linter
import all Mathlib.Basic.Real.Basic
import all Mathlib.Analysis.Normed.Operator.Basic

/-! # Continuous restriction of dual functionals along a bounded linear map -/

@[expose] public section
noncomputable section
open MeasureTheory
namespace HeatKernel

/-- Precomposition by a bounded linear map is a bounded linear map on continuous duals. -/
def dualPrecomposition {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (A : E →L[ℝ] F) :
    (F →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) :=
  (ContinuousLinearMap.lcomp ℝ A).mkContinuous ‖A‖ (fun D => by
    change ‖D.comp A‖ ≤ ‖A‖ * ‖D‖
    exact (ContinuousLinearMap.opNorm_comp_le D A).trans_eq (mul_comm _ _))

/-- The dual precomposition map evaluates by applying the given map first. -/
theorem dualPrecomposition_apply {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (A : E →L[ℝ] F) (D : F →L[ℝ] ℝ) (v : E) :
    dualPrecomposition A D v = D (A v) := rfl

/-- Precomposition preserves Bochner square integrability of dual-valued curves. -/
theorem memLp_dualPrecomposition {E F α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace α]
    {μ : Measure α} (A : E →L[ℝ] F) {D : α → (F →L[ℝ] ℝ)}
    (hD : MemLp D 2 μ) : MemLp (fun t => dualPrecomposition A (D t)) 2 μ :=
  MeasureTheory.MemLp.continuousLinearMap_comp (𝕜 := ℝ)
    (E := F →L[ℝ] ℝ) (F := E →L[ℝ] ℝ) (p := 2) (μ := μ) (f := D)
    hD (dualPrecomposition A)

end HeatKernel
