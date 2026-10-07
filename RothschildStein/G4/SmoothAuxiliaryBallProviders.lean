-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ActualLocalFrameBuffer
public import RothschildStein.G4.ActualAuxiliaryBallVolume
public import RothschildStein.G4.VolumeDoubling

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped BigOperators ENNReal
namespace RothschildStein.G4

/-- Actual local auxiliary-ball volume providers from the
smoothness and bracket-step hypotheses alone. Rank and finite jets
are obtained on a compact original-domain buffer (BB pp. 405–406). -/
theorem exists_smooth_auxiliary_ball_volume_provider {k n s : ℕ}
    (hn : 0 < n) (hs : 0 < s) (w : Fin (k + 1) → ℕ+)
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    (X : Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hstep : bracketStepOn Ω w X s) {z : Fin n → ℝ} (hz : z ∈ Ω) :
    ∃ R c C ε : ℝ, 0 < R ∧ 0 < c ∧ 0 < C ∧ 0 < ε ∧
      closedBall z R ⊆ Ω ∧
      ∀ x ∈ closedBall z (R / 16), ∀ r, 0 < r → r ≤ ε →
        let Λ := volumePolynomial
          (fun B : Fin n → ShortWord w s => frameDet (shortField w X) B x)
          (fun B => ∑ i, (shortWeight w (B i) : ℕ)) r
        ENNReal.ofReal (c * Λ) ≤
          volume {y | auxiliaryDistance (s := s) Ω w X x y < ENNReal.ofReal r} ∧
        volume {y | auxiliaryDistance (s := s) Ω w X x y < ENNReal.ofReal r} ≤
          ENNReal.ofReal (C * Λ) := by
  let h := n * s + s
  let q := h - 1
  have hh : 1 ≤ h := by dsimp [h]; omega
  have hq : q + 1 = n * s + s := by dsimp [q, h] at *; omega
  obtain ⟨R, Δ, M, hR, hΔ, hM, hRΩ, hjets, hmax⟩ :=
    exists_actual_local_frame_buffer hΩ w X hX hstep
      (max (2 * (n * s) + 2 * s) (max ((q + 1) * s) (h + 1 + s))) hz
  obtain ⟨c, C, ε, hc, hC, hε, hvol⟩ :=
    exists_actual_auxiliary_ball_volume_bounds k n s h q hn hs hq (by omega)
      w hM.le hΔ hR Ω hΩ X hX hstep z hRΩ hjets hmax
  exact ⟨R, c, C, ε, hR, hc, hC, hε, hRΩ, hvol⟩

end RothschildStein.G4
