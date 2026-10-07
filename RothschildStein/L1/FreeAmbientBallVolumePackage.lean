-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.FreeBallVolumePackage
public import RothschildStein.L1.CompactDomainBallEquality
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators
namespace RothschildStein.L1

/-- One free reference frame and one fixed threshold provide
both power-volume bounds in every ambient domain containing the free patch.
Freeness and bracket generation are required only on that patch. -/
theorem exists_free_ambient_ball_volume_package_of_local_comparison {k n s : ℕ}
    (hn : 0 < n) (hs : 1 ≤ s) {U K : Set (Fin n → ℝ)}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (w : Fin (k+1) → ℕ+) (hweights : ∀ i, (w i : ℕ) ≤ s)
    (X : Fin (k+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) U)
    (hstep : bracketStepOn U w X s)
    (hcomparison : G1.LocalControlComparison U w X s)
    (hFree : ∀ x ∈ K, FreeAt w s X x) {x₀ : Fin n → ℝ} (hx₀ : x₀ ∈ K) :
    ∃ B : Fin n → G4.ShortWord w s, G4.frameDet (G4.shortField w X) B x₀ ≠ 0 ∧
      ∃ a b aStar bStar r₀ : ℝ,
        0 < a ∧ 0 < b ∧ 0 < aStar ∧ 0 < bStar ∧ 0 < r₀ ∧
        ∀ Ω : Set (Fin n → ℝ), U ⊆ Ω → ∀ x ∈ K, ∀ r : ℝ, 0 < r → r ≤ r₀ →
          let Q := ∑ i, (G4.shortWeight w (B i) : ℕ)
          ENNReal.ofReal (a*r^Q) ≤ volume (rsBall Ω w X x r) ∧
          volume (rsBall Ω w X x r) ≤ ENNReal.ofReal (b*r^Q) ∧
          ENNReal.ofReal (aStar*r^Q) ≤
            volume {y ∈ Ω | G4.auxiliaryDistance (s := s) Ω w X x y < ENNReal.ofReal r} ∧
          volume {y ∈ Ω | G4.auxiliaryDistance (s := s) Ω w X x y < ENNReal.ofReal r} ≤
            ENNReal.ofReal (bStar*r^Q) := by
  obtain ⟨B, hB, a, b, aStar, bStar, r₀, ha, hb, haStar, hbStar, hr₀, hv⟩ :=
    exists_free_ball_volume_package_of_local_comparison hn hs hU hK hKU
      w hweights X hX hstep hcomparison hFree hx₀
  obtain ⟨ρ, hρ, _hρ1, hd⟩ := exists_compact_ball_domain_equalities (s := s) hU hK hKU X hX w
  refine ⟨B, hB, a, b, aStar, bStar, min r₀ ρ, ha, hb, haStar, hbStar,
    lt_min hr₀ hρ, ?_⟩
  intro Ω hUΩ x hx r hr hrr
  have hh := hd Ω hUΩ x hx r hr (hrr.trans (min_le_right _ _))
  have he : rsBall Ω w X x r = rsBall U w X x r := by
    simpa only [rsBall, ordinary_ball_inter_domain_eq] using hh.1
  have hs' : {y ∈ Ω | G4.auxiliaryDistance (s := s) Ω w X x y < ENNReal.ofReal r} =
      {y ∈ U | G4.auxiliaryDistance (s := s) U w X x y < ENNReal.ofReal r} := by
    simpa only [auxiliary_ball_inter_domain_eq] using hh.2
  rw [he, hs']
  exact hv x hx r hr (hrr.trans (min_le_left _ _))
end RothschildStein.L1
