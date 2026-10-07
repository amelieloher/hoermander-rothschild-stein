-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G4.CompactOrdinaryBallDoublingProvider
public import RothschildStein.G1.ActualControlComparison
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace RothschildStein.G4

/-- Compact-center doubling bounds follow from smoothness, a bracket-step
assumption, and local comparison of Euclidean and control topologies
(BB Theorems 9.1 and 9.12, pp. 400, 405). -/
theorem exists_compact_ordinary_ball_doubling_of_smooth_bracketStep {k n s : ℕ}
    (hn : 0 < n) (hs : 1 ≤ s) (w : Fin (k + 1) → ℕ+)
    (hweights : ∀ i, (w i : ℕ) ≤ s)
    {Ω K : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (X : Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hstep : bracketStepOn Ω w X s) :
    ∃ L ε : ℝ, 0 < L ∧ 0 < ε ∧ ∀ x ∈ K,
      (∀ r, 0 < r → r ≤ ε →
        0 < volume {y | controlDistance Ω w X x y < ENNReal.ofReal r} ∧
        volume {y | controlDistance Ω w X x y < ENNReal.ofReal r} < ∞) ∧
      (∀ A r, 1 ≤ A → 0 < r → A * r ≤ ε →
        volume {y | controlDistance Ω w X x y < ENNReal.ofReal (A * r)} ≤
          ENNReal.ofReal (L * A ^ (n * s)) *
            volume {y | controlDistance Ω w X x y < ENNReal.ofReal r}) := by
  exact exists_compact_ordinary_ball_doubling_provider_of_local_comparison hn hs w
    (G3.freeModelData w (by omega) hweights) hweights hΩ hK hKΩ X hX hstep
    (G1.localControlComparison_of_smooth_bracketStep hΩ w X hX hs hweights hstep)
end RothschildStein.G4
