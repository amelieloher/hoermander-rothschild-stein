-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib
public import Hormander.Interface.BasisVec
public import RothschildStein.Definitions.wordBracket
public import RothschildStein.Definitions.BoundedWord
public import RothschildStein.Definitions.boundedWordList
public import RothschildStein.Definitions.FormalRelation

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal NNReal CompactConvergenceCLM
namespace RothschildStein

def FreeAt {a n : ℕ} (p : Fin a → ℕ+) (s : ℕ)
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ) : Prop :=
  ∀ c : BoundedWord a s p → ℝ,
    (∑ I, c I • wordBracket X (boundedWordList I) x) = 0 ↔ FormalRelation c

end RothschildStein
