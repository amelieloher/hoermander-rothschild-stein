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

public import RothschildStein.Definitions.holderENorm
public import RothschildStein.Definitions.hasIntrinsicWordDeriv

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal NNReal

namespace RothschildStein

def intrinsicWordENorm {m n : ℕ}
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (d : (Fin n → ℝ) → (Fin n → ℝ) → ℝ≥0∞)
    (V : Opens (Fin n → ℝ)) (I : List (Fin m)) (α : ℝ)
    (f : (Fin n → ℝ) → ℝ) : ℝ≥0∞ :=
  sInf {r | ∃ g : (Fin n → ℝ) → ℝ,
    hasIntrinsicWordDeriv X V I f g ∧
    r = holderENorm d α (V : Set (Fin n → ℝ)) g}

end RothschildStein
