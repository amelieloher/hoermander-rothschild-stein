-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.WeakFromNash
public import HeatKernel.Sobolev.NormalizedInterpolation
import Mathlib.Tactic

/-!
# Sobolev estimates on an abstract form domain

The measure may be the probability measure obtained by normalizing the measure
of a ball. The energy then includes the squared radius times the normalized
horizontal energy and the normalized quadratic moment. The hypotheses expose
Nash, truncation membership, and energy contraction separately.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace HeatKernel.Sobolev

/-- The weak Sobolev exponent associated with the first-moment exponent in Nash. -/
noncomputable def weakSobolevExponent (b : ℝ) : ℝ := (2 - b) / (1 - b)

/-- The coefficient of the weak tail after iterating the truncated Nash inequality. -/
noncomputable def weakSobolevConstant (N b : ℝ) : ℝ :=
  (2 ^ weakSobolevExponent b * N) ^ (1 / (1 - b))

/-- The squared-norm constant in the strong subcritical Sobolev inequality. -/
noncomputable def subcriticalSobolevConstant (N b q : ℝ) : ℝ :=
  ((1 / (1 - 2 / q) + 1 / (weakSobolevExponent b / q - 1)) *
    weakSobolevConstant N b ^ ((q - 2) / (weakSobolevExponent b - 2))) ^ (2 / q)

/-- The subcritical Sobolev constant is positive for the indicated exponent range. -/
theorem subcriticalSobolevConstant_pos {N b q : ℝ}
    (hN : 0 < N) (hq : 2 < q) (hqp : q < weakSobolevExponent b) :
    0 < subcriticalSobolevConstant N b q := by
  have hq₀ : 0 < q := by linarith
  have hd₁ : 0 < 1 - 2 / q := sub_pos.mpr ((div_lt_one hq₀).mpr hq)
  have hd₂ : 0 < weakSobolevExponent b / q - 1 :=
    sub_pos.mpr ((one_lt_div hq₀).mpr hqp)
  unfold subcriticalSobolevConstant weakSobolevConstant
  positivity

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]

end HeatKernel.Sobolev
