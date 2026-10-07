-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.MappedShortFieldBudget
public import RothschildStein.G4.UniformTimeOneFlow

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped BigOperators

namespace RothschildStein.G4

/-- Actual jointly smooth flows for every mapped short-field family
have a numerical parameter radius independent of the selected frame.
The auxiliary Lipschitz constant does not shrink the prescribed time
interval (BB Lemma 9.49, p. 444; buffered existence argument). -/
theorem exists_uniform_mapped_short_timeOne_flow {k n s m : ℕ}
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
      ∀ a ∈ ball 0 ε, ∀ x ∈ ball x₀ (R / 4),
        Ψ ((a, x), 0) = x ∧ ∀ t ∈ Ioo (-2) 2,
          Ψ ((a, x), t) ∈ closedBall x₀ R ∧
            HasDerivAt (fun v => Ψ ((a, x), v))
              (∑ j, a j • shortField w X (I j) (Ψ ((a, x), t))) t := by
  intro A ε
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (wordJetBase_nonneg_and_le hM).1 _)
  exact exists_uniform_timeOne_flow hΩ (fun j => shortField_contDiffOn hΩ hX (I j))
    x₀ hR hA hRΩ (fun x hx => by
      simpa only [Fintype.card_fin] using sum_mappedShortField_norm_le hΩ hRΩ w X hX I hM hjets hx)

end RothschildStein.G4
