-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.HolderLp
public import Mathlib.Analysis.Normed.Operator.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open MeasureTheory
open scoped ENNReal

/-- Agreement with a bounded Lp operator transfers its norm
bound to the actual input and output representatives. -/
theorem eLpNorm_bound_of_operator_agreement {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (T : Lp ℝ p μ →L[ℝ] Lp ℝ p μ) {C : ℝ} (hT : ‖T‖ ≤ C)
    (v : Lp ℝ p μ) {f g : X → ℝ} (hin : (v : X → ℝ) =ᵐ[μ] f)
    (hout : (T v : X → ℝ) =ᵐ[μ] g) :
    eLpNorm g p μ ≤ ENNReal.ofReal C * eLpNorm f p μ := by
  have hC : 0 ≤ C := (norm_nonneg T).trans hT
  rw [← eLpNorm_congr_ae hout, ← eLpNorm_congr_ae hin, ← Lp.enorm_def, ← Lp.enorm_def,
    ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul hC]
  exact ENNReal.ofReal_le_ofReal
    ((T.le_opNorm v).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg v)))

end RothschildStein.H3
