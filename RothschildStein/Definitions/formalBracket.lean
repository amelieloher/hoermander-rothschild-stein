-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib
public import Hormander.Interface.BasisVec
public import RothschildStein.Definitions.wordConvolution

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal NNReal CompactConvergenceCLM
namespace RothschildStein

def formalBracket {a : ℕ} : List (Fin a) → List (Fin a) → ℝ
  | [] => fun _ => 0
  | [i] => fun J => if J = [i] then 1 else 0
  | i :: j :: I => fun J =>
      wordConvolution (fun K => if K = [i] then 1 else 0) (formalBracket (j :: I)) J -
      wordConvolution (formalBracket (j :: I)) (fun K => if K = [i] then 1 else 0) J

end RothschildStein
