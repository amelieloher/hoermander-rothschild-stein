-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ExpansionDifferentiation

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G4

/-- Ordered differentiation along a list of actual short fields. -/
def shortDerivatives {ι : Type*} {n : ℕ}
    (Z : ι → (Fin n → ℝ) → (Fin n → ℝ)) :
    List ι → ((Fin n → ℝ) → ℝ) → ((Fin n → ℝ) → ℝ)
  | [], f => f
  | L :: M, f => fieldDerivative (Z L) (shortDerivatives Z M f)

/-- Total weight of an ordered short-field differential word. -/
def derivativeWeight {ι : Type*} (w : ι → ℕ+) (M : List ι) : ℤ :=
  (M.map (fun L => ((w L : ℕ) : ℤ))).sum

end RothschildStein.G4
