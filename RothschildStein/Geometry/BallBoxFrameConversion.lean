-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G4.ShortFields
public import RothschildStein.G4.Suboptimality
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators
namespace RothschildStein.Geometry

/-- Literal natural-power suboptimality forces a
nonzero determinant at a spanning point (BB Def. 9.27, p. 420). -/
theorem ballBox_frame_det_ne_zero {m n s : ℕ} (w : Fin m → ℕ+)
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) {x : Fin n → ℝ}
    (hstep : bracketStepOn {x} w X s) {θ r : ℝ} (hθ : 0 < θ) (hr : 0 < r)
    (B : Fin n → List (Fin m))
    (hsub : ∀ B' : Fin n → List (Fin m), (∀ j, wordWeight w (B' j) ≤ s) →
      θ * (|(Matrix.of fun i j => wordBracket X (B' j) x i).det| *
        r ^ (∑ j, wordWeight w (B' j))) ≤
      |(Matrix.of fun i j => wordBracket X (B j) x i).det| *
        r ^ (∑ j, wordWeight w (B j))) :
    (Matrix.of fun i j => wordBracket X (B j) x i).det ≠ 0 := by
  obtain ⟨C,hC⟩ := G4.exists_short_frame hstep (mem_singleton x)
  have hC' : (Matrix.of fun i j => wordBracket X (C j).val x i).det ≠ 0 := hC
  have hbound := hsub (fun j => (C j).val)
    (fun j => ((G4.mem_shortWordFamily_iff w _).mp (C j).property).2)
  have hp := (mul_pos hθ (mul_pos (abs_pos.mpr hC') (pow_pos hr _))).trans_le hbound
  exact abs_pos.mp (pos_of_mul_pos_left hp (pow_nonneg hr.le _))

/-- A literal suboptimal tuple contains only nonempty
words; an empty word is a zero determinant column (BB p. 420). -/
theorem ballBox_frame_words_ne_nil {m n s : ℕ} (w : Fin m → ℕ+)
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) {x : Fin n → ℝ}
    (hstep : bracketStepOn {x} w X s) {θ r : ℝ} (hθ : 0 < θ) (hr : 0 < r)
    (B : Fin n → List (Fin m))
    (hsub : ∀ B' : Fin n → List (Fin m), (∀ j, wordWeight w (B' j) ≤ s) →
      θ * (|(Matrix.of fun i j => wordBracket X (B' j) x i).det| *
        r ^ (∑ j, wordWeight w (B' j))) ≤
      |(Matrix.of fun i j => wordBracket X (B j) x i).det| *
        r ^ (∑ j, wordWeight w (B j))) : ∀ j, B j ≠ [] := by
  intro j hj
  apply ballBox_frame_det_ne_zero w X hstep hθ hr B hsub
  apply Matrix.det_eq_zero_of_column_eq_zero j
  intro i
  simp only [Matrix.of_apply,hj,wordBracket,Pi.zero_apply]

/-- Natural powers in the literal candidate transfer
exactly to the short-word provider's integer-power suboptimality. -/
theorem ballBox_frame_suboptimal_shortWords {m n s : ℕ} (w : Fin m → ℕ+)
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) {x : Fin n → ℝ} {θ r : ℝ}
    (B : Fin n → List (Fin m)) (hB : ∀ j, B j ≠ [] ∧ wordWeight w (B j) ≤ s)
    (hsub : ∀ B' : Fin n → List (Fin m), (∀ j, wordWeight w (B' j) ≤ s) →
      θ * (|(Matrix.of fun i j => wordBracket X (B' j) x i).det| *
        r ^ (∑ j, wordWeight w (B' j))) ≤
      |(Matrix.of fun i j => wordBracket X (B j) x i).det| *
        r ^ (∑ j, wordWeight w (B j))) :
    G4.IsSuboptimal (G4.shortField w X) (G4.shortWeight w)
      (fun j => ⟨B j,(G4.mem_shortWordFamily_iff w _).mpr (hB j)⟩) x θ r := by
  intro C
  have hh := hsub (fun j => (C j).val)
    (fun j => ((G4.mem_shortWordFamily_iff w _).mp (C j).property).2)
  have hCmat : G4.frameDet (G4.shortField w X) C x =
      (Matrix.of fun i j => wordBracket X (C j).val x i).det := rfl
  have hBmat : G4.frameDet (G4.shortField w X)
      (fun j => ⟨B j,(G4.mem_shortWordFamily_iff w _).mpr (hB j)⟩) x =
      (Matrix.of fun i j => wordBracket X (B j) x i).det := rfl
  change θ * (|G4.frameDet (G4.shortField w X) C x| * r ^ G4.frameWeight (G4.shortWeight w) C) ≤ _
  rw [hCmat,hBmat]
  simpa [G4.frameWeight,G4.shortWeight,← Nat.cast_sum] using hh
end RothschildStein.Geometry
