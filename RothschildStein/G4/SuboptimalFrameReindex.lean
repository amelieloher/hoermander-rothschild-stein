-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.FrameReindex
public import RothschildStein.G4.Suboptimality

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace RothschildStein.G4

/-- A finite relabelling preserves suboptimality of the actual
field frame at its original scale (BB Def. 9.27, p. 420). -/
theorem isSuboptimal_reindex {ι σ : Type*} [Fintype ι] [Fintype σ] {n : ℕ}
    (e : ι ≃ σ) (Z : ι → (Fin n → ℝ) → (Fin n → ℝ)) (w : ι → ℕ+)
    (B : Fin n → ι) (x : Fin n → ℝ) (t r : ℝ) :
    IsSuboptimal (fun J => Z (e.symm J)) (fun J => w (e.symm J)) (e ∘ B) x t r ↔
      IsSuboptimal Z w B x t r := by
  constructor
  · intro h C
    simpa only [frameDet_reindex, frameWeight, Function.comp_apply,
      Equiv.symm_apply_apply] using h (e ∘ C)
  · intro h C
    have hC : e ∘ (e.symm ∘ C) = C := by
      funext i
      simp
    have hh := h (e.symm ∘ C)
    rw [← hC]
    simpa only [frameDet_reindex, frameWeight, Function.comp_apply,
      Equiv.symm_apply_apply] using hh

end RothschildStein.G4
