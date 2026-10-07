-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.FrameVolumeAdapters
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators

namespace RothschildStein.L1

/-- [L1-F2] Completing a frame adds exactly the complementary
commutator weights, retaining the prescribed first block. -/
theorem frameWeight_completed_add {ι : Type*} {n m : ℕ} (w : ι → ℕ+)
    (B : Fin n → ι) (C : Fin m → ι) :
    G4.frameWeight w (Fin.addCases B C) = G4.frameWeight w B + G4.frameWeight w C := by
  simp [G4.frameWeight, Fin.sum_univ_add]

/-- [L1-F2] The actual lifted/original frame determinant ratio times
the complementary scale equals the completed/original volume ratio.
Neither determinant factor is dropped (BB pp. 521–522). -/
theorem completed_frame_volume_ratio {ι : Type*} {n m : ℕ}
    (Z : ι → (Fin n → ℝ) → (Fin n → ℝ))
    (Zlift : ι → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ))
    (w : ι → ℕ+) (B : Fin n → ι) (C : Fin m → ι)
    (x : Fin n → ℝ) (ξ : Fin (n + m) → ℝ) {r : ℝ}
    (hr : r ≠ 0) (hB : G4.frameDet Z B x ≠ 0) :
    (|G4.frameDet Zlift (Fin.addCases B C) ξ| / |G4.frameDet Z B x|) *
        r ^ G4.frameWeight w C =
      (|G4.frameDet Zlift (Fin.addCases B C) ξ| *
        r ^ G4.frameWeight w (Fin.addCases B C)) /
      (|G4.frameDet Z B x| * r ^ G4.frameWeight w B) := by
  rw [frameWeight_completed_add, zpow_add₀ hr]
  have hd : |G4.frameDet Z B x| ≠ 0 := abs_ne_zero.mpr hB
  have hp : r ^ G4.frameWeight w B ≠ 0 := zpow_ne_zero _ hr
  field_simp

end RothschildStein.L1
