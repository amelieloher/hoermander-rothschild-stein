-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.OperatorConsequences

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace RothschildStein.P1

/-- The constant jth coordinate field has
homogeneous degree weight(j), on the carrier `Fin N → ℝ` and for all coordinates. -/
theorem coordinateField_homogeneous {N : ℕ} (G : HomogeneousGroup N) (j : Fin N) :
    G2.IsHomogeneousField G (fun _ => Pi.single j 1) ((G.weight j : ℕ) : ℤ) := by
  have h := (G2.isHomogeneousField_iff_operator G
    (fun _ => Hormander.Interface.basisVec j) (G.weight j)).mpr
      (G2.coordinateDerivative_homogeneous G j)
  simpa only [Hormander.Interface.basisVec, Int.cast_natCast] using h

end RothschildStein.P1
