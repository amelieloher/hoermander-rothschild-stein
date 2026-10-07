-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G4.OrdinaryAuxiliaryBallSandwich
public import RothschildStein.G4.SmoothAuxiliaryBallProviders
public import RothschildStein.G4.OrdinaryBallVolumeTransfer
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal BigOperators
namespace RothschildStein.G4
open G3 G1

/-- Original-domain ordinary-ball volume bounds from actual smooth
coefficients and the local comparison of Euclidean and control topologies. -/
theorem exists_smooth_ordinary_ball_volume_provider_of_local_comparison {k n s : ℕ}
    (hn : 0 < n) (hs : 1 ≤ s) (w : Fin (k+1) → ℕ+)
    (D : FreeModelData (k+1) s w) (hw : ∀ i, (w i : ℕ) ≤ s)
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    (X : Fin (k+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hstep : bracketStepOn Ω w X s)
    (hcomparison : LocalControlComparison Ω w X s)
    {z : Fin n → ℝ} (hz : z ∈ Ω) :
    ∃ R c C ε : ℝ, 0 < R ∧ 0 < c ∧ 0 < C ∧ 0 < ε ∧
      closedBall z R ⊆ Ω ∧
      ∀ x ∈ closedBall z (R/16), ∀ r, 0 < r → r ≤ ε →
        let Λ := volumePolynomial
          (fun B : Fin n → ShortWord w s => frameDet (shortField w X) B x)
          (fun B => ∑ i, (shortWeight w (B i) : ℕ)) r
        ENNReal.ofReal (c*Λ) ≤ volume {y | controlDistance Ω w X x y < ENNReal.ofReal r} ∧
        volume {y | controlDistance Ω w X x y < ENNReal.ofReal r} ≤ ENNReal.ofReal (C*Λ) := by
  obtain ⟨R₁, A, ε₁, hR₁, hR₁Ω, hA, hε₁, hb⟩ :=
    exists_ordinary_auxiliary_ball_sandwich_of_local_comparison
      hn hs w D hw hΩ X hX hstep hcomparison hz
  obtain ⟨R₂, c, C, ε₂, hR₂, hc, hC, hε₂, _hR₂Ω, hv⟩ :=
    exists_smooth_auxiliary_ball_volume_provider hn (by omega) w hΩ X hX hstep hz
  let R := min R₁ R₂
  have hR : 0 < R := lt_min hR₁ hR₂
  have hAp : 0 < A := zero_lt_one.trans_le hA
  refine ⟨R, c/A^(n*s), C, min ε₁ ε₂, hR, div_pos hc (pow_pos hAp _),
    hC, lt_min hε₁ hε₂, (closedBall_subset_closedBall (min_le_left _ _)).trans hR₁Ω, ?_⟩
  intro x hx r hr hrε
  have hx₁ : x ∈ closedBall z (R₁/4) :=
    closedBall_subset_closedBall (by have hh := min_le_left R₁ R₂; dsimp [R] at *; linarith) hx
  have hx₂ : x ∈ closedBall z (R₂/16) :=
    closedBall_subset_closedBall (by have hh := min_le_right R₁ R₂; dsimp [R] at *; linarith) hx
  exact ordinary_ball_volume_bounds_of_ball_sandwich volume
    (fun t => {y | auxiliaryDistance (s := s) Ω w X x y < ENNReal.ofReal t})
    (fun t => {y | controlDistance Ω w X x y < ENNReal.ofReal t})
    (fun B : Fin n → ShortWord w s => frameDet (shortField w X) B x)
    (fun B => ∑ i, (shortWeight w (B i) : ℕ))
    (fun B => frame_natural_weight_le (shortWeight w)
      (fun I => ((mem_shortWordFamily_iff w I.val).mp I.property).2) B)
    hA hc hr hrε
    (fun t ht htε => hv x hx₂ t ht (htε.trans (min_le_right _ _)))
    (hb x hx₁ r hr (hrε.trans (min_le_left _ _)))
end RothschildStein.G4
