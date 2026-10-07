-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.OrderedAdjointBinaryWords

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace RothschildStein.G4

/-- Reindexing component fields commutes with the actual ordered
adjoints, including families with repeated selected short fields. -/
theorem orderedAdjoints_map {ι σ : Type*} {n : ℕ}
    (Z : σ → (Fin n → ℝ) → (Fin n → ℝ)) (I : ι → σ)
    (Y : (Fin n → ℝ) → (Fin n → ℝ)) (L : List ι) :
    orderedAdjoints Z (L.map I) Y = orderedAdjoints (fun i => Z (I i)) L Y := by
  induction L with
  | nil => rfl
  | cons i L ih => simp only [List.map_cons, orderedAdjoints, ih]

end RothschildStein.G4
