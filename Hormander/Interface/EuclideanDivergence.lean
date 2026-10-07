-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.Interface.BasisVec

@[expose] public section

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace Hormander.Interface

/-- The Euclidean divergence of a vector field, in the canonical coordinates. -/
def euclideanDivergence {N : ℕ} (V : (Fin N → ℝ) → (Fin N → ℝ))
    (x : Fin N → ℝ) : ℝ :=
  ∑ i : Fin N, (fderiv ℝ V x (basisVec i)) i

end Hormander.Interface
