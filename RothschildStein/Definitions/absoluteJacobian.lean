-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib
public import Hormander.Interface.BasisVec

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal NNReal CompactConvergenceCLM
namespace RothschildStein

def absoluteJacobian {N : ℕ} (f : (Fin N → ℝ) → (Fin N → ℝ))
    (x : Fin N → ℝ) : ℝ :=
  |(LinearMap.toMatrix (Pi.basisFun ℝ (Fin N)) (Pi.basisFun ℝ (Fin N))
    (fderiv ℝ f x).toLinearMap).det|

end RothschildStein
