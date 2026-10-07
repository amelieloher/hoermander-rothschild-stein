-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.Interface.EuclideanDivergence
public import Hormander.Interface.LieAlgebraSpansOn
public import Mathlib.Analysis.Distribution.Distribution
public import Mathlib.Analysis.ODE.Basic
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Data.PNat.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

public import RothschildStein.Definitions.hasIntrinsicDeriv

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal NNReal

namespace RothschildStein

def hasIntrinsicWordDeriv {m n : ℕ}
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (V : Opens (Fin n → ℝ)) :
    List (Fin m) → ((Fin n → ℝ) → ℝ) → ((Fin n → ℝ) → ℝ) → Prop
  | [], f, g => EqOn g f (V : Set (Fin n → ℝ))
  | i :: I, f, g => ∃ h : (Fin n → ℝ) → ℝ,
      hasIntrinsicWordDeriv X V I f h ∧ hasIntrinsicDeriv V (X i) h g

end RothschildStein
