-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Topology.Instances.Rat
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.MeasureTheory.Measure.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Tactic.FunProp

/-!
# Extending ellipticity from rational vectors

A finite quadratic polynomial is continuous in its vector argument. Bounds on rational
vectors therefore extend to all real vectors, on one common set of full measure.
-/

@[expose] public section

open Set MeasureTheory
open scoped BigOperators

namespace HeatKernel

/-- The quadratic expression associated with a real matrix. -/
def matrixEnergy {ι : Type*} [Fintype ι] (a : ι → ι → ℝ) (ξ : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, a i j * ξ j * ξ i

/-- The squared Euclidean length in finite coordinates. -/
def coordinateNormSq {ι : Type*} [Fintype ι] (ξ : ι → ℝ) : ℝ := ∑ i, (ξ i) ^ 2

end HeatKernel
