-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.Distribution.Distribution
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Data.List.FinRange
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Hormander.Interface.BasisVec

public import RothschildStein.Definitions.HomogeneousGroup.dilate

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal NNReal
namespace RothschildStein

def HomogeneousGroup.IsHomogeneousGauge {N : ℕ} (G : HomogeneousGroup N)
    (ν : (Fin N → ℝ) → ℝ) : Prop :=
  Continuous ν ∧ (∀ x, 0 ≤ ν x) ∧
    (∀ x, ν x = 0 ↔ x = 0) ∧
    (∀ t : ℝ, 0 < t → ∀ x, ν (G.dilate t x) = t * ν x)

end RothschildStein
