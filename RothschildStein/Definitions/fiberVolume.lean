-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib
public import Hormander.Interface.BasisVec
public import RothschildStein.Definitions.joinPoint

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal NNReal CompactConvergenceCLM
namespace RothschildStein

def fiberVolume {n m : ℕ} (A : Set (Fin (n + m) → ℝ))
    (z : Fin n → ℝ) : ℝ≥0∞ :=
  volume {t : Fin m → ℝ | joinPoint z t ∈ A}

end RothschildStein
