-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.Interface.LieWord

@[expose] public section

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace Hormander.Interface

/-- Evaluation of a Lie word as a vector field on Euclidean space. -/
def LieWord.eval {k N : ℕ}
    (X : Fin (k + 1) → (Fin N → ℝ) → (Fin N → ℝ)) :
    LieWord k → (Fin N → ℝ) → (Fin N → ℝ)
  | .generator i => X i
  | .bracket p q =>
      VectorField.lieBracket ℝ (LieWord.eval X p) (LieWord.eval X q)

end Hormander.Interface
