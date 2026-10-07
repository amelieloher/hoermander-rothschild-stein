-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G4.OrdinaryGeometryProviders
public import RothschildStein.G4.OrdinaryAuxiliaryBallSandwich
public import RothschildStein.G1.ActualControlComparison
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal
namespace RothschildStein.G4

/-- Actual auxiliary control endpoints have ordinary control
cost bounded linearly by the scale. -/
theorem exists_smooth_auxiliary_ordinary_comparison {k n s : ℕ}
    (hn : 0 < n) (hs : 1 ≤ s) (w : Fin (k+1) → ℕ+)
    (hw : ∀ i, (w i : ℕ) ≤ s)
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    (X : Fin (k+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hstep : bracketStepOn Ω w X s)
    {z : Fin n → ℝ} (hz : z ∈ Ω) :
    ∃ R C η : ℝ, 0 < R ∧ closedBall z R ⊆ Ω ∧ 0 < C ∧ 0 < η ∧
      ∀ x ∈ closedBall z R, ∀ y ∈ closedBall z (R/2),
      ∀ δ : ℝ, 0 < δ → δ < η →
        auxiliaryDistance (s := s) Ω w X x y < ENNReal.ofReal δ →
        controlDistance Ω w X x y ≤ ENNReal.ofReal (C*δ) := by
  exact exists_local_auxiliary_ordinary_provider_of_local_comparison hn hs w hw
    hΩ X hX hstep
    (G1.localControlComparison_of_smooth_bracketStep hΩ w X hX hs hw hstep) hz

/-- Every target endpoint in the open domain satisfies the local two-sided
comparison between ordinary and auxiliary balls, without a patch-membership
hypothesis. -/
theorem exists_smooth_ordinary_auxiliary_ball_sandwich {k n s : ℕ}
    (hn : 0 < n) (hs : 1 ≤ s) (w : Fin (k+1) → ℕ+)
    (hw : ∀ i, (w i : ℕ) ≤ s)
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    (X : Fin (k+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hstep : bracketStepOn Ω w X s)
    {z : Fin n → ℝ} (hz : z ∈ Ω) :
    ∃ R A ε : ℝ, 0 < R ∧ closedBall z R ⊆ Ω ∧ 1 ≤ A ∧ 0 < ε ∧
      ∀ x ∈ closedBall z (R/4), ∀ r : ℝ, 0 < r → r ≤ ε →
      {y | auxiliaryDistance (s := s) Ω w X x y < ENNReal.ofReal (r/A)} ⊆
        {y | controlDistance Ω w X x y < ENNReal.ofReal r} ∧
      {y | controlDistance Ω w X x y < ENNReal.ofReal r} ⊆
        {y | auxiliaryDistance (s := s) Ω w X x y < ENNReal.ofReal r} := by
  exact exists_ordinary_auxiliary_ball_sandwich_of_local_comparison hn hs w
    (G3.freeModelData w (by omega) hw) hw hΩ X hX hstep
    (G1.localControlComparison_of_smooth_bracketStep hΩ w X hX hs hw hstep) hz
end RothschildStein.G4
