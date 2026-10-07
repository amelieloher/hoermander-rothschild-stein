-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.FreeOrdinaryVolumeProvider
public import RothschildStein.L1.FreeAuxiliaryBallVolumeProvider
public import RothschildStein.L1.FreeFrameWeight
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators
namespace RothschildStein.L1

/-- Ordinary and auxiliary free-ball power-volume bounds share one
actual reference frame, one exponent and one radius threshold. -/
theorem exists_free_ball_volume_package_of_local_comparison {k n s : ℕ}
    (hn : 0 < n) (hs : 1 ≤ s) {Ω K : Set (Fin n → ℝ)}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (w : Fin (k+1) → ℕ+) (hweights : ∀ i, (w i : ℕ) ≤ s)
    (X : Fin (k+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hstep : bracketStepOn Ω w X s)
    (hcomparison : G1.LocalControlComparison Ω w X s)
    (hFree : ∀ x ∈ K, FreeAt w s X x) {x₀ : Fin n → ℝ} (hx₀ : x₀ ∈ K) :
    ∃ B : Fin n → G4.ShortWord w s, G4.frameDet (G4.shortField w X) B x₀ ≠ 0 ∧
      ∃ a b aStar bStar r₀ : ℝ,
        0 < a ∧ 0 < b ∧ 0 < aStar ∧ 0 < bStar ∧ 0 < r₀ ∧
        ∀ x ∈ K, ∀ r : ℝ, 0 < r → r ≤ r₀ →
          let Q := ∑ i, (G4.shortWeight w (B i) : ℕ)
          ENNReal.ofReal (a*r^Q) ≤ volume (rsBall Ω w X x r) ∧
          volume (rsBall Ω w X x r) ≤ ENNReal.ofReal (b*r^Q) ∧
          ENNReal.ofReal (aStar*r^Q) ≤
            volume {y ∈ Ω | G4.auxiliaryDistance (s := s) Ω w X x y < ENNReal.ofReal r} ∧
          volume {y ∈ Ω | G4.auxiliaryDistance (s := s) Ω w X x y < ENNReal.ofReal r} ≤
            ENNReal.ofReal (bStar*r^Q) := by
  obtain ⟨B, hB, aStar, bStar, rStar, haStar, hbStar, hrStar, hstar⟩ :=
    exists_free_auxiliary_ball_volume_provider hn (by omega) hΩ hK hKΩ w X hX hstep hFree hx₀
  obtain ⟨B', hB', a, b, r, ha, hb, hr, hord⟩ :=
    exists_free_ordinary_volume_provider_of_local_comparison hn hs hΩ hK hKΩ
      w hweights X hX hstep hcomparison hFree hx₀
  have hw := short_frameWeight_eq_of_FreeAt X x₀ (hFree x₀ hx₀) B' B hB' hB
  rw [G4.frameWeight_eq_nat_sum, G4.frameWeight_eq_nat_sum] at hw
  have hw' : (∑ i, (G4.shortWeight w (B' i) : ℕ)) =
      ∑ i, (G4.shortWeight w (B i) : ℕ) := by exact_mod_cast hw
  refine ⟨B, hB, a, b, aStar, bStar, min r rStar, ha, hb, haStar, hbStar,
    lt_min hr hrStar, ?_⟩
  intro x hx t ht htr
  have ho := hord x hx t ht (htr.trans (min_le_left _ _))
  rw [hw'] at ho
  have hs' := hstar x hx t ht (htr.trans (min_le_right _ _))
  exact ⟨ho.1, ho.2, hs'.1, hs'.2⟩
end RothschildStein.L1
