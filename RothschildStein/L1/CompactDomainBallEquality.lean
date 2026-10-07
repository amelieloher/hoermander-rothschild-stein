-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.CompactAmbientBuffer
public import RothschildStein.G4.AuxiliaryControl

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped ENNReal

namespace RothschildStein.L1

/-- First exit proves equality of small ambient and patch balls,
not merely containment. This permits applying patch estimates to the
original distance without changing its definition. -/
theorem exists_compact_controlBall_domain_equality {a n : ℕ}
    {U K : Set (Fin n → ℝ)} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) U) (w : Fin a → ℕ+) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ 1 ∧
      ∀ Ω : Set (Fin n → ℝ), U ⊆ Ω → ∀ x ∈ K,
        ∀ r : ℝ, 0 < r → r ≤ r₀ →
          {y | controlDistance Ω w X x y < ENNReal.ofReal r} =
            {y | controlDistance U w X x y < ENNReal.ofReal r} := by
  obtain ⟨r₀, hr₀, hr1, hstay⟩ := exists_compact_ambient_curve_buffer hU hK hKU X hX w
  refine ⟨r₀, hr₀, hr1, ?_⟩
  intro Ω hUΩ x hx r hr hrr
  ext y
  constructor
  · intro hy
    obtain ⟨δ, _hδ, hδr, γ, hγ, hγ0, hγ1⟩ :=
      G1.exists_controlledCurve_of_controlDistance_lt hy
    have hmap := hstay Ω δ (hδr.le.trans hrr) γ hγ (hγ0 ▸ hx)
    have hγU : isControlledCurve U w X δ γ :=
      ⟨hγ.1, hγ.2.1, hmap, hγ.2.2.2⟩
    have hd := G1.controlDistance_le_of_curve hγU
    rw [hγ0, hγ1] at hd
    exact hd.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hr).mpr hδr)
  · intro hy
    exact (G1.controlDistance_mono_domain w X hUΩ x y).trans_lt hy

/-- The same domain equality holds simultaneously for ordinary
and starred balls, with one threshold before every compact center and
application radius (BB pp. 519–522). -/
theorem exists_compact_ball_domain_equalities {a n s : ℕ}
    {U K : Set (Fin n → ℝ)} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) U) (w : Fin a → ℕ+) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ 1 ∧
      ∀ Ω : Set (Fin n → ℝ), U ⊆ Ω → ∀ x ∈ K,
        ∀ r : ℝ, 0 < r → r ≤ r₀ →
          {y | controlDistance Ω w X x y < ENNReal.ofReal r} =
            {y | controlDistance U w X x y < ENNReal.ofReal r} ∧
          {y | G4.auxiliaryDistance (s := s) Ω w X x y < ENNReal.ofReal r} =
            {y | G4.auxiliaryDistance (s := s) U w X x y < ENNReal.ofReal r} := by
  obtain ⟨ρ, hρ, hρ1, hball⟩ := exists_compact_controlBall_domain_equality hU hK hKU X hX w
  let Z := fun j : Fin (Fintype.card (G4.ShortWord w s)) =>
    G4.shortField w X (G4.shortIndex (s := s) w j)
  let v := fun j : Fin (Fintype.card (G4.ShortWord w s)) =>
    G4.shortWeight w (G4.shortIndex (s := s) w j)
  have hZ : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (Z j) U :=
    fun j => G4.shortField_contDiffOn hU hX (G4.shortIndex (s := s) w j)
  obtain ⟨σ, hσ, _hσ1, hstar⟩ := exists_compact_controlBall_domain_equality hU hK hKU Z hZ v
  refine ⟨min ρ σ, lt_min hρ hσ, (min_le_left _ _).trans hρ1, ?_⟩
  intro Ω hUΩ x hx r hr hrr
  exact ⟨hball Ω hUΩ x hx r hr (hrr.trans (min_le_left _ _)),
    hstar Ω hUΩ x hx r hr (hrr.trans (min_le_right _ _))⟩

end RothschildStein.L1
