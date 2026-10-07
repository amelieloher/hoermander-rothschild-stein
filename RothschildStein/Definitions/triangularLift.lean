-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib
public import Hormander.Interface.BasisVec
public import RothschildStein.Definitions.basePoint

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal NNReal CompactConvergenceCLM
namespace RothschildStein

def triangularLift {a n m : ℕ}
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ))
    (P : Fin a → Fin m → MvPolynomial (Fin (n + m)) ℝ) :
    Fin a → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) :=
  fun i ξ => Fin.addCases (X i (basePoint ξ)) (fun l => MvPolynomial.eval ξ (P i l))

end RothschildStein
