-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Geometry.Manifold.VectorField.LieBracket
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.Topology.Algebra.Support

@[expose] public section

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace Hormander.Interface

/-- The `i`-th standard basis vector of `Fin N → ℝ`. -/
def basisVec {d : ℕ} (i : Fin d) : Fin d → ℝ := Pi.single i (1 : ℝ)

end Hormander.Interface
