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

def rsGauge {N : ℕ} (ω : Fin N → ℕ) (_hω : ∀ j, 0 < ω j)
    (u : Fin N → ℝ) : ℝ :=
  sSup (Set.range (fun j => Real.rpow |u j| ((ω j : ℝ)⁻¹)))

end RothschildStein
