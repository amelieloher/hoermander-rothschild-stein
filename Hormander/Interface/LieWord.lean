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

/-- An iterated Lie word in the drift and squared vector-field generators. -/
inductive LieWord (k : ℕ) where
  | generator : Fin (k + 1) → LieWord k
  | bracket : LieWord k → LieWord k → LieWord k

end Hormander.Interface
