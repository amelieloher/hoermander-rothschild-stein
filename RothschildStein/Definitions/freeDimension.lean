-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib
public import Hormander.Interface.BasisVec
public import RothschildStein.Definitions.formalSpan

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal NNReal CompactConvergenceCLM
namespace RothschildStein

def freeDimension (a s : ℕ) (p : Fin a → ℕ+) : ℕ :=
  Module.finrank ℝ (formalSpan a s p)

end RothschildStein
