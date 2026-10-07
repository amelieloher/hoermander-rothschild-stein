-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.CriticalFamilyFreezingBound

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.P1.LiftedChart
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m}

/-- In the actual input chart, endpoint freezing
improves the critical pole by one order, uniformly on compact center sets. -/
theorem exists_criticalFamily_chartFreezing_bound
    {D : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → SmoothDifferentialOperator (n + m)}
    (F : SplitFamily C.G D) (Γ : (Fin (n + m) → ℝ) → ℝ)
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) Γ {(0 : Fin (n + m) → ℝ)}ᶜ)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u : Fin (n + m) → ℝ, u ≠ 0 →
      Γ (C.G.dilate r u) = r ^ (2 - (C.G.homogeneousDimension : ℝ)) * Γ u)
    {K : Set (Fin (n + m) → ℝ)} (hK : IsCompact K) (hKU : K ⊆ C.U) :
    ∃ ε M : ℝ, 0 < ε ∧ 0 ≤ M ∧ ∀ ξ ∈ K, ∀ η ∈ C.U, ξ ≠ η →
      kgauge C.G (C.Θ η ξ) ≤ ε →
      ‖(D ξ η).apply Γ (C.Θ η ξ) - (D ξ ξ).apply Γ (C.Θ η ξ)‖ ≤
        M * kgauge C.G (C.Θ η ξ) ^ (1 - (C.G.homogeneousDimension : ℤ)) := by
  obtain ⟨ε, M, hε, hM, hb⟩ := exists_criticalFamily_freezing_bound F Γ hΓ hhom hK hKU
  refine ⟨ε, M, hε, hM, ?_⟩
  intro ξ hξ η hη hne hsmall
  have hu : C.Θ η ξ ≠ 0 := (C.theta_eq_zero_iff hη (hKU hξ)).not.mpr hne
  have hi : (C.e ξ).symm (-C.Θ η ξ) = η := by
    rw [C.theta_antisymm ξ (hKU hξ) η hη, neg_neg]
    exact symm_theta (hKU hξ) hη
  simpa only [hi] using hb ξ hξ (C.Θ η ξ) hu hsmall

end RothschildStein.P1.LiftedChart
