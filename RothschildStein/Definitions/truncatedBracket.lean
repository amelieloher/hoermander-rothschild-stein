-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib
public import Hormander.Interface.BasisVec
public import RothschildStein.Definitions.boundedWordList
public import RothschildStein.Definitions.WordCoefficients
public import RothschildStein.Definitions.formalBracket

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal NNReal CompactConvergenceCLM
namespace RothschildStein

def truncatedBracket {a s : ℕ} {p : Fin a → ℕ+} (I : List (Fin a)) :
    WordCoefficients a s p := fun J => formalBracket I (boundedWordList J)

end RothschildStein
