-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.FreePointDilation
public import RothschildStein.L1.FrameWeightEigenvalues
public import RothschildStein.L1.ShortFreeFramePatterns
public import RothschildStein.G4.Suboptimality

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators

namespace RothschildStein.L1

/-- All actual nonzero bounded-word frames at a free point have
one common weight, without an additional common-weight hypothesis. -/
theorem bounded_frame_weight_eq_of_FreeAt {a n s : ℕ} {w : Fin a → ℕ+}
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ)
    (hFree : FreeAt w s X x) (B C : Fin n → BoundedWord a s w)
    (hB : G4.frameDet (fun I => wordBracket X (boundedWordList I)) B x ≠ 0)
    (hC : G4.frameDet (fun I => wordBracket X (boundedWordList I)) C x ≠ 0) :
    (∑ j, wordWeight w (boundedWordList (B j))) =
      ∑ j, wordWeight w (boundedWordList (C j)) := by
  obtain ⟨D, hD⟩ := exists_freePoint_dilation X x hFree B hB 2
  exact frame_weight_eq_of_dilation (fun I => wordBracket X (boundedWordList I))
    (fun I => wordWeight w (boundedWordList I)) B C x hB hC D hD

/-- The common weight conclusion for G4's actual short-word
frames, in the exact integer-valued frame-weight interface. -/
theorem short_frameWeight_eq_of_FreeAt {a n s : ℕ} {w : Fin a → ℕ+}
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ)
    (hFree : FreeAt w s X x) (B C : Fin n → G4.ShortWord w s)
    (hB : G4.frameDet (G4.shortField w X) B x ≠ 0)
    (hC : G4.frameDet (G4.shortField w X) C x ≠ 0) :
    G4.frameWeight (G4.shortWeight w) B = G4.frameWeight (G4.shortWeight w) C := by
  let B' : Fin n → BoundedWord a s w := fun j =>
    ⟨(B j).val, (Finset.mem_filter.mp (B j).property).1⟩
  let C' : Fin n → BoundedWord a s w := fun j =>
    ⟨(C j).val, (Finset.mem_filter.mp (C j).property).1⟩
  have hh := bounded_frame_weight_eq_of_FreeAt X x hFree B' C' hB hC
  have hi := congrArg (fun k : ℕ => (k : ℤ)) hh
  simpa [G4.frameWeight, G4.shortWeight, boundedWordList, B', C', Nat.cast_sum] using hi

/-- Fixing a reference frame at one free point gives the common
weight at every free point of the patch. -/
theorem short_frameWeight_eq_reference_on_free_patch {a n s : ℕ}
    {w : Fin a → ℕ+} (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ))
    {K : Set (Fin n → ℝ)} {x₀ : Fin n → ℝ} (hx₀ : FreeAt w s X x₀)
    (hFree : ∀ x ∈ K, FreeAt w s X x) (B : Fin n → G4.ShortWord w s)
    (hB : G4.frameDet (G4.shortField w X) B x₀ ≠ 0) :
    ∀ x ∈ K, ∀ C : Fin n → G4.ShortWord w s,
      G4.frameDet (G4.shortField w X) C x ≠ 0 →
        G4.frameWeight (G4.shortWeight w) C = G4.frameWeight (G4.shortWeight w) B := by
  intro x hx C hC
  have hBx := (short_frameDet_ne_zero_iff_of_FreeAt X hx₀ (hFree x hx) B).mp hB
  exact short_frameWeight_eq_of_FreeAt X x (hFree x hx) C B hC hBx

end RothschildStein.L1
