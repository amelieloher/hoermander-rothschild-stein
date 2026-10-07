-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.Interface.EuclideanDivergence

@[expose] public section

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace Hormander.Interface

/-- The formal adjoint applied to a smooth compactly supported test function. -/
def hormanderAdjointTest {k N : ℕ}
    (X : Fin (k + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (c : (Fin N → ℝ) → ℝ) (φ : (Fin N → ℝ) → ℝ)
    (x : Fin N → ℝ) : ℝ :=
  -euclideanDivergence (fun y => φ y • X 0 y) x +
    ∑ i : Fin k,
      euclideanDivergence
        (fun y =>
          euclideanDivergence (fun q => φ q • X i.succ q) y • X i.succ y)
        x +
    c x * φ x

end Hormander.Interface
