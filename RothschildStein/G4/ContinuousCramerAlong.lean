-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.Frames
public import Mathlib.Topology.Instances.Matrix

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace RothschildStein.G4

/-- Actual Cramer coordinates vary continuously along continuous
frame columns and velocities, wherever the actual determinant is nonzero. -/
theorem continuous_frameCoefficient_along {P ι : Type*} [TopologicalSpace P] {n : ℕ}
    (Z : ι → (Fin n → ℝ) → (Fin n → ℝ)) (B : Fin n → ι)
    (g V : P → (Fin n → ℝ))
    (hcolumns : ∀ j, Continuous (fun p => Z (B j) (g p)))
    (hV : Continuous V) (hdet : ∀ p, frameDet Z B (g p) ≠ 0) (i : Fin n) :
    Continuous (fun p => frameCoefficient Z B (fun _ => V p) i (g p)) := by
  classical
  have hmatrix : Continuous (fun p => frameMatrix Z B (g p)) :=
    continuous_pi (fun k => continuous_pi (fun j =>
      (continuous_apply k).comp (hcolumns j)))
  exact ((hmatrix.matrix_updateCol i hV).matrix_det).div hmatrix.matrix_det hdet

end RothschildStein.G4
