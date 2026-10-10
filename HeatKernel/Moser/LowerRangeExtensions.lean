-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Linter

/-! # Differentiable extensions from a lower bounded scalar range

Clipping the derivative at the lower endpoint and integrating gives an extension with
Lipschitz derivative. The fundamental theorem of calculus identifies it with the original
function on the lower bounded range.
-/

@[expose] public section

open Set MeasureTheory
open scoped NNReal

namespace HeatKernel

/-- Clipping the argument preserves a Lipschitz bound on a lower bounded range. -/
theorem lipschitzWith_clipped_derivative {D : ℝ → ℝ} {L : ℝ≥0} {c : ℝ}
    (hD : LipschitzOnWith L D (Ici c)) : LipschitzWith L (fun x => D (max c x)) := by
  have hmax := LipschitzWith.id.const_max c
  apply LipschitzWith.of_dist_le_mul
  intro x y
  exact (hD.dist_le_mul (max c x) (le_max_left _ _) (max c y) (le_max_left _ _)).trans
    (mul_le_mul_of_nonneg_left (by simpa using hmax.dist_le_mul x y) L.coe_nonneg)

end HeatKernel
