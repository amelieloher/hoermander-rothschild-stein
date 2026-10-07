-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.MappedBufferedTimeOneFlow
public import RothschildStein.G4.ActualCoefficientRemainderNorm

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped BigOperators

namespace RothschildStein.G4

/-- The actual mapped-flow derivative remainder is bounded using
primitive jets on the prescribed closed ball. Open-buffer containment
and the forward initial-patch condition are consequences of the numerical
radius, including at zero coefficients (BB pp. 441–444). -/
theorem norm_buffered_mapped_coefficient_remainder_le {k n s m h : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (w : Fin (k + 1) → ℕ+)
    (X : Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (X j) Ω) (I : Fin m → ShortWord w s)
    (x₀ : Fin n → ℝ) {R δ M : ℝ} (hR : 0 < R) (hδ : 0 < δ) (hM : 0 ≤ M)
    (hRΩ : closedBall x₀ R ⊆ Ω)
    (hjets : ∀ j, HasJetBound Ω (closedBall x₀ R) (X j) (h + 1 + s) M)
    (hδR : δ ≤ R / (64 * (1 + (m : ℝ) * wordJetBase n 0 s M ^ s)))
    (Φ : (((Fin m → ℝ) × (Fin n → ℝ)) × ℝ) → (Fin n → ℝ))
    (hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) Φ
      ((ball 0 δ ×ˢ ball x₀ (R / 4)) ×ˢ Ioo (-2) 2))
    (hΦ : ∀ a ∈ ball 0 δ, ∀ x ∈ ball x₀ (R / 4), Φ ((a, x), 0) = x ∧
      ∀ t ∈ Ioo (-2 : ℝ) 2, Φ ((a, x), t) ∈ closedBall x₀ R ∧
        HasDerivAt (fun v => Φ ((a, x), v))
          (∑ j, a j • shortField w X (I j) (Φ ((a, x), t))) t)
    (z : Fin m → ℝ) (hz : z ∈ ball 0 δ) (hznorm : ‖z‖ ≤ 1) (i : Fin m)
    {x : Fin n → ℝ} (hx : x ∈ ball x₀ (R / 8))
    (q : ℕ) (hq : q + 1 ≤ h)
    (hsmall : RothschildStein.G1.spatialJetRate (h + 1)
      ((m : ℝ) * 2 ^ (h + 1) * (h + 1).factorial *
        (wordJetBase n (h + 1) s M ^ s) * ‖z‖) < 1) :
    let W := fun j => shortField w X (I j)
    let Z : ((Fin m → ℝ) × (Fin n → ℝ)) → (Fin n → ℝ) :=
      fun p => ∑ j, p.1 j • W j p.2
    let Y : ((Fin m → ℝ) × (Fin n → ℝ)) → (Fin n → ℝ) := fun p => W i p.2
    let B := wordJetBase n (h + 1) s M ^ s
    let C := (2 ^ (h + 2) * ((m : ℝ) * 2 ^ (h + 1) * (h + 1).factorial * B)) ^ (q + 1) *
      ((h + 1).factorial * B)
    ‖fderiv ℝ (fun a => Φ ((a, x), 1)) z (Pi.single i 1) -
      ∑ j ∈ Finset.range (q + 1), ((-1 : ℝ) ^ j / ((j + 1).factorial : ℝ)) •
        (((spatialBracketFamily Z)^[j] Y) (z, Φ ((z, x), 1)))‖ ≤
      (2 * C) * ‖z‖ ^ (q + 1) := by
  intro W Z Y B C
  let A := (m : ℝ) * wordJetBase n 0 s M ^ s
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (wordJetBase_nonneg_and_le hM).1 _)
  have hbound : ∀ y ∈ closedBall x₀ R, ∑ j, ‖W j y‖ ≤ A := by
    intro y hy
    simpa only [Fintype.card_fin] using sum_mappedShortField_norm_le hΩ hRΩ w X hX I hM
      (fun j => (hjets j).mono (by omega)) hy
  have hballΩ : ball x₀ R ⊆ Ω := ball_subset_closedBall.trans hRΩ
  have hUΩ : ball x₀ (R / 4) ⊆ ball x₀ R := ball_subset_ball (by linarith)
  have hflow : ∀ p ∈ ball 0 δ ×ˢ ball x₀ (R / 4), Φ (p, 0) = p.2 ∧
      ∀ t ∈ Ioo (-2 : ℝ) 2,
        HasDerivAt (fun v => Φ (p, v)) (∑ j, p.1 j • W j (Φ (p, t))) t ∧
          Φ (p, t) ∈ ball x₀ R := by
    intro p hp
    refine ⟨(hΦ p.1 hp.1 p.2 hp.2).1, ?_⟩
    intro t ht
    exact ⟨(hΦ p.1 hp.1 p.2 hp.2).2 t ht |>.2,
      numerical_timeOne_open_buffer W x₀ hR hδ hA hδR Φ hΦ hbound hp.1 hp.2 ht⟩
  have hjet : ∀ y ∈ ball x₀ R, ∀ j, ∀ l ≤ h + 1,
      ‖iteratedFDeriv ℝ l (W j) y‖ ≤ B := by
    intro y hy j l hl
    have hb := mappedShortField_jet_bound hΩ hRΩ w X hX I hM hjets j l hl y
      (ball_subset_closedBall hy)
    simpa only [iteratedFDerivWithin_of_isOpen _ hΩ (hballΩ hy)] using hb
  exact norm_original_coefficient_remainder_le_including_zero isOpen_ball isOpen_ball
    isOpen_ball hUΩ W (fun j => (shortField_contDiffOn hΩ hX (I j)).mono hballΩ)
    z hz hznorm i (by norm_num : (1 : ℝ) < 2) Φ hsmooth.continuousOn hflow
    (ball_subset_ball (by linarith) hx)
    (numerical_timeOne_forward_buffer W x₀ hR hδ hA hδR Φ hΦ hbound hz hx)
    (pow_nonneg (wordJetBase_nonneg_and_le hM).1 _) hjet hsmall q hq

end RothschildStein.G4
