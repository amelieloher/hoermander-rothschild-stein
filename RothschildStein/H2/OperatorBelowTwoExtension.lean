-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.OperatorInterpolation
public import RothschildStein.H2.OperatorLpExtension

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace RothschildStein.H2
variable {X : Type*} [MeasurableSpace X]

/-- The explicit Marcinkiewicz norm constant for interpolation. -/
def operatorInterpolationConstant (C cT p : ℝ) : ℝ :=
  (p * (2 * C / (p - 1) + 4 * cT ^ 2 / (2 - p))) ^ (1 / p)

end RothschildStein.H2
