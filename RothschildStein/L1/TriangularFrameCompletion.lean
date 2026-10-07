-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.FrameCompletion
public import RothschildStein.L1.TriangularBracketProjection
public import RothschildStein.G4.ShortFields

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.L1

/-- An actual original short frame lifts to an independent
family because its horizontal projection is the original frame. -/
theorem short_triangularLift_frame_linearIndependent {a n m s : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (w : Fin a → ℕ+)
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (P : Fin a → Fin m → MvPolynomial (Fin (n + m)) ℝ)
    (ξ : Fin (n + m) → ℝ) (hξ : ξ ∈ basePoint ⁻¹' Ω)
    (B : Fin n → G4.ShortWord w s)
    (hB : G4.frameDet (G4.shortField w X) B (basePoint ξ) ≠ 0) :
    LinearIndependent ℝ (fun j => G4.shortField w (triangularLift X P) (B j) ξ) := by
  have hli := (frameDet_ne_zero_iff_linearIndependent (G4.shortField w X) B (basePoint ξ)).mp hB
  apply LinearIndependent.of_comp (P1.paddingBaseCLM n m).toLinearMap
  have hp : ((P1.paddingBaseCLM n m).toLinearMap ∘
      (fun j => G4.shortField w (triangularLift X P) (B j) ξ)) =
        (fun j => G4.shortField w X (B j) (basePoint ξ)) := by
    funext j
    change (P1.paddingBaseCLM n m) (wordBracket (triangularLift X P) (B j).val ξ) =
      wordBracket X (B j).val (basePoint ξ)
    rw [P1.paddingBaseCLM_apply]
    exact wordBracket_triangularLift_projection hΩ X hX P (B j).val ξ hξ
  rw [hp]
  exact hli

/-- Complete any actual original short frame with lifted short
commutators, retaining the original words in the first n columns. -/
theorem exists_short_triangularLift_frame_completion {a n m s : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (w : Fin a → ℕ+)
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (P : Fin a → Fin m → MvPolynomial (Fin (n + m)) ℝ)
    (ξ : Fin (n + m) → ℝ) (hξ : ξ ∈ basePoint ⁻¹' Ω)
    (hstep : bracketStepOn {ξ} w (triangularLift X P) s)
    (B : Fin n → G4.ShortWord w s)
    (hB : G4.frameDet (G4.shortField w X) B (basePoint ξ) ≠ 0) :
    ∃ C : Fin m → G4.ShortWord w s,
      G4.frameDet (G4.shortField w (triangularLift X P)) (Fin.addCases B C) ξ ≠ 0 := by
  have hli := short_triangularLift_frame_linearIndependent hΩ w X hX P ξ hξ B hB
  have hset : Set.range (fun I : G4.ShortWord w s => G4.shortField w (triangularLift X P) I ξ) =
      {v | ∃ I : List (Fin a), I ≠ [] ∧ wordWeight w I ≤ s ∧
        v = wordBracket (triangularLift X P) I ξ} := by
    ext v
    constructor
    · rintro ⟨I, rfl⟩
      obtain ⟨hne, hw⟩ := (G4.mem_shortWordFamily_iff w I.val).mp I.property
      exact ⟨I.val, hne, hw, rfl⟩
    · rintro ⟨I, hne, hw, rfl⟩
      exact ⟨⟨I, (G4.mem_shortWordFamily_iff w I).mpr ⟨hne, hw⟩⟩, rfl⟩
  apply exists_frame_completion (G4.shortField w (triangularLift X P)) ξ B hli
  rw [hset]
  exact hstep ξ (Set.mem_singleton ξ)

end RothschildStein.L1
