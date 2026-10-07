-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.FreeFramePatterns
public import RothschildStein.G4.ShortFields

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace RothschildStein.L1

/-- The actual nonempty short-word frame pattern is invariant
throughout a free patch, directly from `FreeAt`. -/
theorem short_frameDet_ne_zero_iff_of_FreeAt {a n s : ℕ} {w : Fin a → ℕ+}
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ))
    {x y : Fin n → ℝ} (hx : FreeAt w s X x) (hy : FreeAt w s X y)
    (B : Fin n → G4.ShortWord w s) :
    G4.frameDet (G4.shortField w X) B x ≠ 0 ↔ G4.frameDet (G4.shortField w X) B y ≠ 0 := by
  let C : Fin n → BoundedWord a s w := fun j =>
    ⟨(B j).val, (Finset.mem_filter.mp (B j).property).1⟩
  have hh := frameDet_ne_zero_iff_of_FreeAt X hx hy C
  exact hh

end RothschildStein.L1
