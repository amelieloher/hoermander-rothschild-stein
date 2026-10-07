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

public import RothschildStein.Definitions.fieldTranspose

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal NNReal

namespace RothschildStein

def sumSquaresWithDriftTranspose {q n : ℕ}
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (φ : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  fieldTranspose (X 0) φ x +
    ∑ i : Fin q, fieldTranspose (X i.succ) (fieldTranspose (X i.succ) φ) x

end RothschildStein
