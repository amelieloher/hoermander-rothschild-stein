-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.Frames
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace RothschildStein.L1

/-- The shared actual frame determinant is nonzero exactly
when its field values form an independent family. -/
theorem frameDet_ne_zero_iff_linearIndependent {ι : Type*} {N : ℕ}
    (Z : ι → (Fin N → ℝ) → (Fin N → ℝ)) (B : Fin N → ι) (x : Fin N → ℝ) :
    G4.frameDet Z B x ≠ 0 ↔ LinearIndependent ℝ (fun j => Z (B j) x) := by
  rw [G4.frameDet, ← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det,
    ← Matrix.linearIndependent_cols_iff_isUnit]
  rfl

end RothschildStein.L1
