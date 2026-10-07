-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.Distribution.Distribution
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Data.List.FinRange
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Hormander.Interface.BasisVec

public import RothschildStein.Definitions.SmoothDifferentialOperator.apply
public import RothschildStein.Definitions.HomogeneousGroup.dilate

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal NNReal
namespace RothschildStein

def SmoothDifferentialOperator.IsHomogeneous {N : ℕ}
    (D : SmoothDifferentialOperator N) (G : HomogeneousGroup N) (degree : ℝ) : Prop :=
  ∀ f : (Fin N → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) f →
    ∀ t : ℝ, 0 < t → ∀ x,
      D.apply (f ∘ G.dilate t) x = t ^ degree * D.apply f (G.dilate t x)

end RothschildStein
