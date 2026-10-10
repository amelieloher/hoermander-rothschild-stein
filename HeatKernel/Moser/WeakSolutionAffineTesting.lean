-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Tactic
import all Mathlib.Basic.Real.Basic
import all Mathlib.Analysis.Normed.Operator.Basic
import all Mathlib.Analysis.Normed.Operator.NormedSpace
import all Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-! # Affine combinations of nonlinear and fixed-test endpoint balances -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory
namespace HeatKernel

/-- A nonlinear endpoint balance and its fixed-test linear correction combine
into the balance with the affine-corrected test. -/
theorem affine_energy_sub_eq_integral_of_endpoint_identities {α E : Type*}
    [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : α → (E →L[ℝ] ℝ)} {P : α → E} (hF : MemLp F 2 μ) (hP : MemLp P 2 μ)
    {a b l r : ℝ} (w : E) (c : ℝ)
    (hn : a - b = ∫ t, F t (P t) ∂μ) (hl : l - r = ∫ t, F t w ∂μ) :
    (a + c * l) - (b + c * r) = ∫ t, F t (P t + c • w) ∂μ := by
  let D := ContinuousLinearMap.id ℝ (E →L[ℝ] ℝ)
  have hi : Integrable (fun t => F t (P t)) μ :=
    (D.memLp_of_bilin 1 hF hP).integrable (by norm_num)
  have hw : Integrable (fun t => F t w) μ :=
    ((ContinuousLinearMap.apply ℝ ℝ w).comp_memLp' hF).integrable (by norm_num)
  simp only [map_add, map_smul, smul_eq_mul]
  rw [integral_add hi (hw.const_mul c), integral_const_mul, ← hn, ← hl]
  ring

end HeatKernel
