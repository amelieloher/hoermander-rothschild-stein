-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib
public import Hormander.Interface.BasisVec
public import RothschildStein.Definitions.wordWeight
public import RothschildStein.Definitions.WordCoefficients
public import RothschildStein.Definitions.truncatedBracket

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal NNReal CompactConvergenceCLM
namespace RothschildStein

def formalSpan (a s : ℕ) (p : Fin a → ℕ+) : Submodule ℝ (WordCoefficients a s p) :=
  Submodule.span ℝ { f | ∃ I : List (Fin a), I ≠ [] ∧ wordWeight p I ≤ s ∧
    f = truncatedBracket I }

end RothschildStein
