-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G4.AuxiliaryOrdinaryComparison
public import RothschildStein.G4.CompactOrdinaryBallDoublingProvider
public import RothschildStein.G3.FreeModels
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal BigOperators
namespace RothschildStein.G4
open G3 G1

/-- The free model gives local ordinary-cost bounds under the local
comparison of Euclidean and control topologies. -/
theorem exists_local_auxiliary_ordinary_provider_of_local_comparison {k n s : ℕ}
    (hn : 0 < n) (hs : 1 ≤ s) (w : Fin (k+1) → ℕ+)
    (hw : ∀ i, (w i : ℕ) ≤ s)
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    (X : Fin (k+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hstep : bracketStepOn Ω w X s)
    (hcomparison : LocalControlComparison Ω w X s)
    {z : Fin n → ℝ} (hz : z ∈ Ω) :
    ∃ R C η : ℝ, 0 < R ∧ closedBall z R ⊆ Ω ∧ 0 < C ∧ 0 < η ∧
      ∀ x ∈ closedBall z R, ∀ y ∈ closedBall z (R/2),
      ∀ δ : ℝ, 0 < δ → δ < η →
        auxiliaryDistance (s := s) Ω w X x y < ENNReal.ofReal δ →
        controlDistance Ω w X x y ≤ ENNReal.ofReal (C*δ) := by
  exact exists_local_auxiliary_ordinary_comparison_of_local_comparison hn hs w (G3.freeModelData w (by omega) hw) hw hΩ X hX hstep hcomparison hz

/-- The free model gives local ordinary-cost bounds under the local
comparison of Euclidean and control topologies. -/
theorem exists_compact_ordinary_volume_provider_of_local_comparison {k n s : ℕ}
    (hn : 0 < n) (hs : 1 ≤ s) (w : Fin (k + 1) → ℕ+)
    (hweights : ∀ i, (w i : ℕ) ≤ s)
    {Ω K : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (X : Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hstep : bracketStepOn Ω w X s)
    (hcomparison : G1.LocalControlComparison Ω w X s) :
    ∃ c C ε : ℝ, 0 < c ∧ 0 < C ∧ 0 < ε ∧
      ∀ x ∈ K, ∀ r, 0 < r → r ≤ ε →
        let Λ := volumePolynomial
          (fun B : Fin n → ShortWord w s => frameDet (shortField w X) B x)
          (fun B => ∑ i, (shortWeight w (B i) : ℕ)) r
        ENNReal.ofReal (c * Λ) ≤
          volume {y | controlDistance Ω w X x y < ENNReal.ofReal r} ∧
        volume {y | controlDistance Ω w X x y < ENNReal.ofReal r} ≤
          ENNReal.ofReal (C * Λ) := by
  exact exists_compact_ordinary_ball_volume_provider_of_local_comparison hn hs w (G3.freeModelData w (by omega) hweights) hweights hΩ hK hKΩ X hX hstep hcomparison

end RothschildStein.G4
