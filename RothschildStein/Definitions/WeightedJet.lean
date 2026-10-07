-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib
public import Hormander.Interface.BasisVec
public import RothschildStein.Definitions.rsPartial

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal NNReal CompactConvergenceCLM
namespace RothschildStein

def WeightedJet {N : ℕ} (ω : Fin N → ℕ) (a : ℤ)
    (R : (Fin N → ℝ) → (Fin N → ℝ)) : Prop :=
  ∀ j J, (((J.map ω).sum) : ℤ) < a + (ω j : ℤ) →
    rsPartial J (fun u => R u j) 0 = 0

end RothschildStein
