-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.TriangularFrameCompletion
public import RothschildStein.L1.CompactFreeGeometry

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.L1

/-- A single positive strict suboptimality constant works for
all original frames and their actual lifted completions on a compact free
patch, at every positive scale (BB pp. 519–520). -/
theorem exists_uniform_triangularLift_frame_completion {a n m s : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) {K : Set (Fin (n + m) → ℝ)}
    (hK : IsCompact K) (hKΩ : K ⊆ basePoint ⁻¹' Ω) (w : Fin a → ℕ+)
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (P : Fin a → Fin m → MvPolynomial (Fin (n + m)) ℝ)
    (hFree : ∀ ξ ∈ K, FreeAt w s (triangularLift X P) ξ)
    (hstep : bracketStepOn K w (triangularLift X P) s)
    {ξ₀ : Fin (n + m) → ℝ} (hξ₀ : ξ₀ ∈ K) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ ∀ ξ ∈ K, ∀ B : Fin n → G4.ShortWord w s,
      G4.frameDet (G4.shortField w X) B (basePoint ξ) ≠ 0 →
      ∃ C : Fin m → G4.ShortWord w s,
        G4.frameDet (G4.shortField w (triangularLift X P)) (Fin.addCases B C) ξ ≠ 0 ∧
        ∀ r : ℝ, 0 < r → G4.IsSuboptimal (G4.shortField w (triangularLift X P))
          (G4.shortWeight w) (Fin.addCases B C) ξ t r := by
  have hU : IsOpen (basePoint (n := n) (m := m) ⁻¹' Ω) := by
    have hb : Continuous (basePoint (n := n) (m := m)) :=
      (P1.paddingBaseCLM n m).continuous
    exact hΩ.preimage hb
  obtain ⟨R, hR⟩ := G4.exists_short_frame hstep hξ₀
  obtain ⟨t, ht, ht1, hsub⟩ := exists_uniform_short_suboptimality_of_FreeAt hU hK hKΩ w
    (triangularLift X P) (fun i => contDiffOn_triangularLift X hX P i) hFree hξ₀ R hR
  refine ⟨t / 2, by positivity, by linarith, ?_⟩
  intro ξ hξ B hB
  have hs : bracketStepOn {ξ} w (triangularLift X P) s := by
    intro y hy
    have he : y = ξ := Set.mem_singleton_iff.mp hy
    subst y
    exact hstep ξ hξ
  obtain ⟨C, hC⟩ := exists_short_triangularLift_frame_completion hΩ w X hX P ξ (hKΩ hξ) hs B hB
  refine ⟨C, hC, ?_⟩
  intro r hr D
  have hh := hsub ξ hξ (Fin.addCases B C) hC r hr D
  apply le_trans _ hh
  apply mul_le_mul_of_nonneg_right (by linarith : t / 2 ≤ t)
  exact mul_nonneg (abs_nonneg _) (zpow_nonneg hr.le _)

end RothschildStein.L1
