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

def rsPartial {N : ℕ} : List (Fin N) → ((Fin N → ℝ) → ℝ) → (Fin N → ℝ) → ℝ
  | [] => fun f => f
  | j :: J => fun f u => fderiv ℝ (rsPartial J f) u (Pi.single j 1)

end RothschildStein
