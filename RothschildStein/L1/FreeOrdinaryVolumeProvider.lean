-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.FreeOrdinaryBallVolumeProvider
public import RothschildStein.G3.FreeModels
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators
namespace RothschildStein.L1

/-- The concrete free model is selected internally for the actual
compact free ordinary-ball power-volume consequence. -/
theorem exists_free_ordinary_volume_provider_of_local_comparison {k n s : ℕ}
    (hn : 0 < n) (hs : 1 ≤ s) {Ω K : Set (Fin n → ℝ)}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (w : Fin (k + 1) → ℕ+)
    (hweights : ∀ i, (w i : ℕ) ≤ s)
    (X : Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hstep : bracketStepOn Ω w X s)
    (hcomparison : G1.LocalControlComparison Ω w X s) (hFree : ∀ x ∈ K, FreeAt w s X x)
    {x₀ : Fin n → ℝ} (hx₀ : x₀ ∈ K) :
    ∃ B : Fin n → G4.ShortWord w s, G4.frameDet (G4.shortField w X) B x₀ ≠ 0 ∧
      ∃ A D r₀ : ℝ, 0 < A ∧ 0 < D ∧ 0 < r₀ ∧
        ∀ x ∈ K, ∀ r, 0 < r → r ≤ r₀ →
          ENNReal.ofReal (A * r ^ (∑ i, (G4.shortWeight w (B i) : ℕ))) ≤
            volume {y ∈ Ω | controlDistance Ω w X x y < ENNReal.ofReal r} ∧
          volume {y ∈ Ω | controlDistance Ω w X x y < ENNReal.ofReal r} ≤
            ENNReal.ofReal (D * r ^ (∑ i, (G4.shortWeight w (B i) : ℕ))) := by
  exact exists_free_ordinary_ball_volume_provider_of_local_comparison hn hs hΩ hK hKΩ w
    (G3.freeModelData w (by omega) hweights) hweights X hX hstep hcomparison hFree hx₀
end RothschildStein.L1
