-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.NumericalOpenBuffer

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped BigOperators

namespace RothschildStein.G4

/-- The mapped short-field flow has both an open primitive-jet
buffer for all times and the forward initial-patch buffer needed by the
actual coefficient remainder. Its radius depends only on the numerical
field budget and prescribed clearance (BB Lemma 9.49, pp. 441–444). -/
theorem exists_uniform_mapped_buffered_timeOne_flow {k n s m : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (w : Fin (k + 1) → ℕ+)
    (X : Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (X j) Ω) (I : Fin m → ShortWord w s)
    (x₀ : Fin n → ℝ) {R M : ℝ} (hR : 0 < R) (hM : 0 ≤ M)
    (hRΩ : closedBall x₀ R ⊆ Ω)
    (hjets : ∀ j, HasJetBound Ω (closedBall x₀ R) (X j) s M) :
    let A := (m : ℝ) * wordJetBase n 0 s M ^ s
    let ε := R / (64 * (1 + A))
    ∃ Ψ : (((Fin m → ℝ) × (Fin n → ℝ)) × ℝ) → (Fin n → ℝ),
      ContDiffOn ℝ (⊤ : ℕ∞) Ψ ((ball 0 ε ×ˢ ball x₀ (R / 4)) ×ˢ Ioo (-2) 2) ∧
      (∀ a ∈ ball 0 ε, ∀ x ∈ ball x₀ (R / 4),
        Ψ ((a, x), 0) = x ∧ ∀ t ∈ Ioo (-2) 2,
          Ψ ((a, x), t) ∈ ball x₀ R ∧
            HasDerivAt (fun v => Ψ ((a, x), v))
              (∑ j, a j • shortField w X (I j) (Ψ ((a, x), t))) t) ∧
      ∀ a ∈ ball 0 ε, ∀ x ∈ ball x₀ (R / 8), ∀ t ∈ Icc (0 : ℝ) 1,
        Ψ ((a, x), t) ∈ ball x₀ (R / 4) := by
  intro A ε
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (wordJetBase_nonneg_and_le hM).1 _)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hbound : ∀ y ∈ closedBall x₀ R,
      ∑ j, ‖shortField w X (I j) y‖ ≤ A := by
    intro y hy
    simpa only [Fintype.card_fin] using
      sum_mappedShortField_norm_le hΩ hRΩ w X hX I hM hjets hy
  obtain ⟨Ψ, hsmooth, hflow⟩ := exists_uniform_mapped_short_timeOne_flow
    hΩ w X hX I x₀ hR hM hRΩ hjets
  refine ⟨Ψ, hsmooth, ?_, ?_⟩
  · intro a ha x hx
    refine ⟨(hflow a ha x hx).1, ?_⟩
    intro t ht
    exact ⟨numerical_timeOne_open_buffer (fun j => shortField w X (I j))
      x₀ hR hε hA le_rfl Ψ hflow hbound ha hx ht, (hflow a ha x hx).2 t ht |>.2⟩
  · intro a ha x hx t ht
    exact numerical_timeOne_forward_buffer (fun j => shortField w X (I j))
      x₀ hR hε hA le_rfl Ψ hflow hbound ha hx t ht

end RothschildStein.G4
