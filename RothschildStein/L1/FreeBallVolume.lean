-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.FreeFrameWeight
public import RothschildStein.G4.CommonWeightVolume
public import RothschildStein.G4.FrameVolumeAdapters
public import RothschildStein.G4.AuxiliaryControl
public import RothschildStein.Definitions.rsBall

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators

namespace RothschildStein.L1

/-- Freeness (`FreeAt`) turns the explicit frame-polynomial
volume comparison for starred balls into uniform power growth.
The volume comparison is a hypothesis (BB Cor 10.37, pp. 515–516). -/
theorem exists_free_auxiliary_ball_volume_bounds_of_frame_volume_bounds
    {a n s : ℕ} {Ω K : Set (Fin n → ℝ)}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (w : Fin a → ℕ+) (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hFree : ∀ x ∈ K, FreeAt w s X x) {x₀ : Fin n → ℝ} (hx₀ : x₀ ∈ K)
    (B : Fin n → G4.ShortWord w s)
    (hB : G4.frameDet (G4.shortField (s := s) w X) B x₀ ≠ 0)
    {c C r₀ : ℝ} (hc : 0 < c) (hC : 0 < C)
    (hvol : ∀ x ∈ K, ∀ r, 0 < r → r ≤ r₀ →
      ENNReal.ofReal (c * (G4.volumePolynomial (fun D => G4.frameDet (G4.shortField (s := s) w X) D x)
        (fun D : Fin n → G4.ShortWord w s => ∑ i, (G4.shortWeight w (D i) : ℕ)) r)) ≤ volume ({y ∈ Ω | G4.auxiliaryDistance (s := s) Ω w X x y < ENNReal.ofReal r}) ∧
        volume ({y ∈ Ω | G4.auxiliaryDistance (s := s) Ω w X x y < ENNReal.ofReal r}) ≤ ENNReal.ofReal (C * (G4.volumePolynomial (fun D => G4.frameDet (G4.shortField (s := s) w X) D x)
        (fun D : Fin n → G4.ShortWord w s => ∑ i, (G4.shortWeight w (D i) : ℕ)) r))) :
    ∃ A D : ℝ, 0 < A ∧ 0 < D ∧ ∀ x ∈ K, ∀ r, 0 < r → r ≤ r₀ →
      ENNReal.ofReal (A * r ^ (∑ i, (G4.shortWeight w (B i) : ℕ))) ≤ volume ({y ∈ Ω | G4.auxiliaryDistance (s := s) Ω w X x y < ENNReal.ofReal r}) ∧
        volume ({y ∈ Ω | G4.auxiliaryDistance (s := s) Ω w X x y < ENNReal.ofReal r}) ≤ ENNReal.ofReal (D * r ^ (∑ i, (G4.shortWeight w (B i) : ℕ))) := by
  have hnonzero : ∀ x ∈ K, ∃ D : Fin n → G4.ShortWord w s,
      G4.frameDet (G4.shortField w X) D x ≠ 0 := by
    intro x hx
    exact ⟨B, (short_frameDet_ne_zero_iff_of_FreeAt X (hFree x₀ hx₀) (hFree x hx) B).mp hB⟩
  have hweight : ∀ x ∈ K, ∀ D : Fin n → G4.ShortWord w s,
      G4.frameDet (G4.shortField w X) D x ≠ 0 →
        (∑ i, (G4.shortWeight w (D i) : ℕ)) = ∑ i, (G4.shortWeight w (B i) : ℕ) := by
    intro x hx D hD
    have hh := short_frameWeight_eq_reference_on_free_patch X (hFree x₀ hx₀) hFree B hB x hx D hD
    rw [G4.frameWeight_eq_nat_sum, G4.frameWeight_eq_nat_sum] at hh
    exact_mod_cast hh
  exact G4.exists_commonWeight_volume_bounds_of_volumePolynomial_bounds hK volume
    (fun x r => {y ∈ Ω | G4.auxiliaryDistance (s := s) Ω w X x y < ENNReal.ofReal r})
    (G4.frameDet (G4.shortField (s := s) w X))
    (fun D : Fin n → G4.ShortWord w s => ∑ i, (G4.shortWeight w (D i) : ℕ))
    (∑ i, (G4.shortWeight w (B i) : ℕ))
    (fun D => (G4.frameDet_contDiffOn (fun I => G4.shortField_contDiffOn hΩ hX I) D).continuousOn.mono hKΩ)
    hnonzero hweight hc hC hvol

/-- Freeness (`FreeAt`) turns the explicit frame-polynomial
volume comparison for control balls into uniform power growth.
The volume comparison is a hypothesis (BB Cor 10.37, pp. 515–516). -/
theorem exists_free_control_ball_volume_bounds_of_frame_volume_bounds
    {a n s : ℕ} {Ω K : Set (Fin n → ℝ)}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (w : Fin a → ℕ+) (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hFree : ∀ x ∈ K, FreeAt w s X x) {x₀ : Fin n → ℝ} (hx₀ : x₀ ∈ K)
    (B : Fin n → G4.ShortWord w s)
    (hB : G4.frameDet (G4.shortField (s := s) w X) B x₀ ≠ 0)
    {c C r₀ : ℝ} (hc : 0 < c) (hC : 0 < C)
    (hvol : ∀ x ∈ K, ∀ r, 0 < r → r ≤ r₀ →
      ENNReal.ofReal (c * (G4.volumePolynomial (fun D => G4.frameDet (G4.shortField (s := s) w X) D x)
        (fun D : Fin n → G4.ShortWord w s => ∑ i, (G4.shortWeight w (D i) : ℕ)) r)) ≤ volume (rsBall Ω w X x r) ∧
        volume (rsBall Ω w X x r) ≤ ENNReal.ofReal (C * (G4.volumePolynomial (fun D => G4.frameDet (G4.shortField (s := s) w X) D x)
        (fun D : Fin n → G4.ShortWord w s => ∑ i, (G4.shortWeight w (D i) : ℕ)) r))) :
    ∃ A D : ℝ, 0 < A ∧ 0 < D ∧ ∀ x ∈ K, ∀ r, 0 < r → r ≤ r₀ →
      ENNReal.ofReal (A * r ^ (∑ i, (G4.shortWeight w (B i) : ℕ))) ≤ volume (rsBall Ω w X x r) ∧
        volume (rsBall Ω w X x r) ≤ ENNReal.ofReal (D * r ^ (∑ i, (G4.shortWeight w (B i) : ℕ))) := by
  have hnonzero : ∀ x ∈ K, ∃ D : Fin n → G4.ShortWord w s,
      G4.frameDet (G4.shortField w X) D x ≠ 0 := by
    intro x hx
    exact ⟨B, (short_frameDet_ne_zero_iff_of_FreeAt X (hFree x₀ hx₀) (hFree x hx) B).mp hB⟩
  have hweight : ∀ x ∈ K, ∀ D : Fin n → G4.ShortWord w s,
      G4.frameDet (G4.shortField w X) D x ≠ 0 →
        (∑ i, (G4.shortWeight w (D i) : ℕ)) = ∑ i, (G4.shortWeight w (B i) : ℕ) := by
    intro x hx D hD
    have hh := short_frameWeight_eq_reference_on_free_patch X (hFree x₀ hx₀) hFree B hB x hx D hD
    rw [G4.frameWeight_eq_nat_sum, G4.frameWeight_eq_nat_sum] at hh
    exact_mod_cast hh
  exact G4.exists_commonWeight_volume_bounds_of_volumePolynomial_bounds hK volume
    (rsBall Ω w X)
    (G4.frameDet (G4.shortField (s := s) w X))
    (fun D : Fin n → G4.ShortWord w s => ∑ i, (G4.shortWeight w (D i) : ℕ))
    (∑ i, (G4.shortWeight w (B i) : ℕ))
    (fun D => (G4.frameDet_contDiffOn (fun I => G4.shortField_contDiffOn hΩ hX I) D).continuousOn.mono hKΩ)
    hnonzero hweight hc hC hvol

end RothschildStein.L1
