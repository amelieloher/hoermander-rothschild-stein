-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.WeightedTaylorParameters

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped Topology

namespace RothschildStein.P1

variable {N : ℕ}

/-- Composition of coordinate derivatives concatenates the index lists. -/
theorem rsPartial_concat (I J : List (Fin N)) (f : (Fin N → ℝ) → ℝ) :
    rsPartial I (rsPartial J f) = rsPartial (I ++ J) f := by
  induction I with
  | nil => rfl
  | cons i I ih =>
    change (fun u => fderiv ℝ (rsPartial I (rsPartial J f)) u (Pi.single i 1)) = _
    rw [ih]
    rfl

end RothschildStein.P1
