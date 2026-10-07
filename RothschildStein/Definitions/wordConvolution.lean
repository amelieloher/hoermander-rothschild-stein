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

def wordConvolution {a : ℕ} (f g : List (Fin a) → ℝ) (J : List (Fin a)) : ℝ :=
  ∑ r ∈ Finset.range (J.length + 1), f (J.take r) * g (J.drop r)

end RothschildStein
