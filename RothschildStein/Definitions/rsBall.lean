-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib
public import Hormander.Interface.BasisVec
public import RothschildStein.Definitions.controlDistance

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal NNReal CompactConvergenceCLM
namespace RothschildStein

def rsBall {a n : ℕ} (Ω : Set (Fin n → ℝ))
    (p : Fin a → ℕ+) (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ))
    (x : Fin n → ℝ) (r : ℝ) : Set (Fin n → ℝ) :=
  {y ∈ Ω | controlDistance Ω p X x y < ENNReal.ofReal r}

end RothschildStein
