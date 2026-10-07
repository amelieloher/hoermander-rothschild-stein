-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib
public import Hormander.Interface.BasisVec
public import RothschildStein.Definitions.BoundedWord

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal NNReal CompactConvergenceCLM
namespace RothschildStein

def boundedWordList {a s : ℕ} {p : Fin a → ℕ+} (I : BoundedWord a s p) :
    List (Fin a) := I.val

end RothschildStein
