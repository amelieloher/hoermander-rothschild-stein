-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Definitions.SmoothDifferentialOperator.apply
public import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open scoped BigOperators
namespace RothschildStein.P1

/-- Reflection of the finite smooth-coefficient differential
operator from BB (11.12), p. 546. The sign uses ordinary order, while
homogeneous degree uses the separate group weights. -/
def differentialReflection {N : ℕ} (P : SmoothDifferentialOperator N) :
    SmoothDifferentialOperator N where
  indices := P.indices
  coefficient a x := (-1 : ℝ) ^ (∑ j, a j) * P.coefficient a (-x)
  smooth_coefficient := by
    intro a ha
    exact contDiff_const.mul ((P.smooth_coefficient a ha).comp contDiff_neg)

/-- Reflection keeps exactly the same effective multi-indices. -/
theorem differentialReflection_indices {N : ℕ} (P : SmoothDifferentialOperator N) :
    (differentialReflection P).indices = P.indices := rfl

/-- The reflected coefficient contains the precise parity sign. -/
theorem differentialReflection_coefficient {N : ℕ} (P : SmoothDifferentialOperator N)
    (a : Fin N → ℕ) (x : Fin N → ℝ) :
    (differentialReflection P).coefficient a x =
      (-1 : ℝ) ^ (∑ j, a j) * P.coefficient a (-x) := rfl

end RothschildStein.P1
