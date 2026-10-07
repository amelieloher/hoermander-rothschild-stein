-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib
public import Hormander.Interface.BasisVec
public import RothschildStein.Definitions.wordWeight
public import RothschildStein.Definitions.wordBracket

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal NNReal CompactConvergenceCLM
namespace RothschildStein

def StepSpansAt {a n : ℕ} (p : Fin a → ℕ+) (s : ℕ)
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ) : Prop :=
  Submodule.span ℝ { v | ∃ I : List (Fin a), I ≠ [] ∧ wordWeight p I ≤ s ∧
    v = wordBracket X I x } = ⊤

end RothschildStein
