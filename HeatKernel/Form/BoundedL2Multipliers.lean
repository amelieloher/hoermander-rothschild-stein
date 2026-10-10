-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.ScalarComposition
import Mathlib.Tactic.Linter

/-! # Bounded measurable multiplication on L² -/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace HeatKernel

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {a : α → ℝ} {C : ℝ}

/-- Multiplication by a bounded measurable coefficient on L². -/
def boundedL2Mul (ha : AEStronglyMeasurable a μ) (hC : 0 ≤ C)
    (hb : ∀ᵐ x ∂μ, ‖a x‖ ≤ C) (u : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  (memLp_mul_of_ae_bound ha (Lp.memLp u) hC hb).toLp (fun x => a x * u x)

/-- The bounded multiplication map has the expected representative. -/
theorem boundedL2Mul_ae (ha : AEStronglyMeasurable a μ) (hC : 0 ≤ C)
    (hb : ∀ᵐ x ∂μ, ‖a x‖ ≤ C) (u : Lp ℝ 2 μ) :
    boundedL2Mul ha hC hb u =ᵐ[μ] (fun x => a x * u x) :=
  (memLp_mul_of_ae_bound ha (Lp.memLp u) hC hb).coeFn_toLp

/-- A bounded coefficient preserves convergence in L². -/
theorem tendsto_boundedL2Mul (ha : AEStronglyMeasurable a μ) (hC : 0 ≤ C)
    (hb : ∀ᵐ x ∂μ, ‖a x‖ ≤ C) {u : ℕ → Lp ℝ 2 μ} {v : Lp ℝ 2 μ}
    (hu : Tendsto u atTop (𝓝 v)) :
    Tendsto (fun n => boundedL2Mul ha hC hb (u n)) atTop (𝓝 (boundedL2Mul ha hC hb v)) := by
  exact tendsto_L2_mul_of_bounded (fun _ => ha) ha hC (fun _ => hb) hb
    (Eventually.of_forall fun _ => tendsto_const_nhds) hu
    (fun n => boundedL2Mul_ae ha hC hb (u n)) (boundedL2Mul_ae ha hC hb v)


end HeatKernel
