-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.ContinuousBochnerCompositionLimits
import Mathlib.Tactic.Linter

/-! # Continuous composition maps on Bochner L² spaces -/

@[expose] public section

noncomputable section

open MeasureTheory Filter TopologicalSpace
open scoped NNReal ENNReal Topology

namespace HeatKernel

variable {T E F : Type*} [MeasurableSpace T] (μ : Measure T)
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F]
    {P : E → F} (hP : Continuous P) {C : ℝ≥0} (hb : ∀ u, ‖P u‖ ≤ (C : ℝ) * ‖u‖)

/-- A continuous map with linear growth acts on Bochner L² equivalence classes. -/
def continuousBochnerComposition (v : Lp E 2 μ) : Lp F 2 μ :=
  (memLp_comp_of_continuous_norm_le hP hb (Lp.memLp v)).toLp (fun t => P (v t))

/-- The Bochner composition is represented by the pointwise composition almost everywhere. -/
theorem continuousBochnerComposition_coeFn_ae (v : Lp E 2 μ) :
    continuousBochnerComposition μ hP hb v =ᵐ[μ] fun t => P (v t) :=
  (memLp_comp_of_continuous_norm_le hP hb (Lp.memLp v)).coeFn_toLp

/-- Continuous maps with linear growth act continuously on Bochner L² over finite measure spaces. -/
theorem continuous_continuousBochnerComposition [IsFiniteMeasure μ] :
    Continuous (continuousBochnerComposition μ hP hb) := by
  apply continuous_iff_seqContinuous.mpr
  intro v u hv
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mpr
  apply (tendsto_eLpNorm_comp_of_tendsto_Lp hP hb hv).congr
  intro n
  exact (eLpNorm_congr_ae ((continuousBochnerComposition_coeFn_ae μ hP hb (v n)).sub
    (continuousBochnerComposition_coeFn_ae μ hP hb u))).symm

end HeatKernel
