-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.FreeFrameWeight
public import RothschildStein.L1.UniformFreeFrames
public import RothschildStein.G4.ShortFields

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.L1

private theorem free_frame_family {a n s : ℕ} {w : Fin a → ℕ+}
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ)) {K : Set (Fin n → ℝ)}
    (hFree : ∀ x ∈ K, FreeAt w s X x) {x₀ : Fin n → ℝ} (hx₀ : x₀ ∈ K)
    (B : Fin n → G4.ShortWord w s) (hB : G4.frameDet (G4.shortField (s := s) w X) B x₀ ≠ 0) :
    ∃ F : Finset (Fin n → G4.ShortWord w s),
      (∀ C ∈ F, ∀ x ∈ K, G4.frameDet (G4.shortField (s := s) w X) C x ≠ 0) ∧
      (∀ C, C ∉ F → ∀ x ∈ K, G4.frameDet (G4.shortField (s := s) w X) C x = 0) ∧
      (∀ C ∈ F, G4.frameWeight (G4.shortWeight (s := s) w) C = G4.frameWeight (G4.shortWeight (s := s) w) B) ∧
      B ∈ F := by
  classical
  let F : Finset (Fin n → G4.ShortWord w s) := Finset.univ.filter (fun C => G4.frameDet (G4.shortField (s := s) w X) C x₀ ≠ 0)
  have hF (C) : C ∈ F ↔ G4.frameDet (G4.shortField (s := s) w X) C x₀ ≠ 0 := by simp [F]
  refine ⟨F, ?_, ?_, ?_, (hF B).mpr hB⟩
  · intro C hC x hx
    exact (short_frameDet_ne_zero_iff_of_FreeAt X (hFree x₀ hx₀) (hFree x hx) C).mp
      ((hF C).mp hC)
  · intro C hC x hx
    by_contra hz
    exact hC ((hF C).mpr
      ((short_frameDet_ne_zero_iff_of_FreeAt X (hFree x₀ hx₀) (hFree x hx) C).mpr hz))
  · intro C hC
    exact short_frameWeight_eq_of_FreeAt X x₀ (hFree x₀ hx₀) C B ((hF C).mp hC) hB

/-- Freeness (`FreeAt`) gives the common weight and makes
every nonzero short frame uniformly suboptimal on a compact patch. -/
theorem exists_uniform_short_suboptimality_of_FreeAt {a n s : ℕ}
    {Ω K : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (w : Fin a → ℕ+) (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hFree : ∀ x ∈ K, FreeAt w s X x) {x₀ : Fin n → ℝ} (hx₀ : x₀ ∈ K)
    (B : Fin n → G4.ShortWord w s) (hB : G4.frameDet (G4.shortField (s := s) w X) B x₀ ≠ 0) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ ∀ x ∈ K, ∀ C : Fin n → G4.ShortWord w s,
      G4.frameDet (G4.shortField (s := s) w X) C x ≠ 0 → ∀ r : ℝ, 0 < r →
        G4.IsSuboptimal (G4.shortField (s := s) w X) (G4.shortWeight (s := s) w) C x t r := by
  classical
  obtain ⟨F, hn, hz, hw, hBF⟩ := free_frame_family X hFree hx₀ B hB
  obtain ⟨t, ht, ht1, hh⟩ := exists_uniform_free_frame_suboptimality hK
    (G4.shortField (s := s) w X) (G4.shortWeight (s := s) w)
    (fun I => (G4.shortField_contDiffOn hΩ hX I).continuousOn.mono hKΩ)
    F (G4.frameWeight (G4.shortWeight (s := s) w) B) hn hz hw
  refine ⟨t, ht, ht1, ?_⟩
  intro x hx C hC r hr
  have hCF : C ∈ F := by by_contra hc; exact hC (hz C hc x hx)
  exact hh x hx C hCF r hr

end RothschildStein.L1
