-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.Distribution.Distribution
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Data.List.FinRange
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Hormander.Interface.BasisVec

public import RothschildStein.Definitions.SmoothDifferentialOperator
public import RothschildStein.Definitions.euclideanPartial

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal NNReal
namespace RothschildStein

def SmoothDifferentialOperator.apply {N : ℕ} (D : SmoothDifferentialOperator N)
    (f : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) : ℝ :=
  ∑ a ∈ D.indices, D.coefficient a x * euclideanPartial a f x

end RothschildStein
