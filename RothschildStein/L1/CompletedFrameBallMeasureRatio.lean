-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.AmbientOrdinaryVolumeUnconditional
public import RothschildStein.L1.CompletedFrameMeasureRatio
public import RothschildStein.L1.FreeOrdinaryBallVolumeProvider
public import RothschildStein.Definitions.triangularLift
public import RothschildStein.P1.PaddingCoordinates
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace RothschildStein.L1

/-- Actual local original and lifted geometry supplies both
completed-frame ball-volume-ratio estimates. The two volume-polynomial
premises are constructed uniformly over compact centers and every
containing ambient path domain (BB pp. 521–522, (10.49)). -/
theorem exists_completed_frame_ball_measure_ratio {k n m s : ℕ}
    (hn : 0 < n) (hs : 1 ≤ s) (w : Fin (k+1) → ℕ+)
    (hw : ∀ i, (w i : ℕ) ≤ s)
    {Uo : Set (Fin n → ℝ)} {Ul K : Set (Fin (n+m) → ℝ)}
    (hUo : IsOpen Uo) (hUl : IsOpen Ul) (hK : IsCompact K) (hKUl : K ⊆ Ul)
    (hKUo : basePoint '' K ⊆ Uo)
    (X : Fin (k+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (P : Fin (k+1) → Fin m → MvPolynomial (Fin (n+m)) ℝ)
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Uo)
    (hXl : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (triangularLift X P i) Ul)
    (hstep : bracketStepOn Uo w X s)
    (hstepl : bracketStepOn Ul w (triangularLift X P) s)
    {t : ℝ} (ht : 0 < t) :
    ∃ c C r₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < r₀ ∧
      ∀ Ω : Set (Fin n → ℝ), Uo ⊆ Ω → Ul ⊆ basePoint ⁻¹' Ω →
      ∀ ξ ∈ K, ∀ r : ℝ, 0 < r → r ≤ r₀ →
      ∀ B : Fin n → G4.ShortWord w s, ∀ J : Fin m → G4.ShortWord w s,
      G4.frameDet (G4.shortField w X) B (basePoint ξ) ≠ 0 →
      G4.IsSuboptimal (G4.shortField w X) (G4.shortWeight w) B (basePoint ξ) (1/2) r →
      G4.IsSuboptimal (G4.shortField w (triangularLift X P)) (G4.shortWeight w)
        (Fin.addCases B J) ξ t r →
      let R := (|G4.frameDet (G4.shortField w (triangularLift X P)) (Fin.addCases B J) ξ| /
        |G4.frameDet (G4.shortField w X) B (basePoint ξ)|) * r ^ G4.frameWeight (G4.shortWeight w) J
      let H := volume (rsBall (basePoint ⁻¹' Ω) w (triangularLift X P) ξ r) /
        volume (rsBall Ω w X (basePoint ξ) r)
      ENNReal.ofReal c * ENNReal.ofReal R ≤ H ∧ H ≤ ENNReal.ofReal C * ENNReal.ofReal R := by
  have hBase : Continuous (basePoint (n := n) (m := m)) := (P1.paddingBaseCLM n m).continuous
  obtain ⟨co,Co,ro,hco,hCo,hro,hvo⟩ := exists_compact_ambient_ordinary_volume_provider
    hn hs w hw hUo (hK.image hBase) hKUo X hX hstep
  obtain ⟨cl,Cl,rl,hcl,hCl,hrl,hvl⟩ := exists_compact_ambient_ordinary_volume_provider
    (by omega : 0 < n+m) hs w hw hUl hK hKUl (triangularLift X P) hXl hstepl
  let No := (Fintype.card (Fin n → G4.ShortWord w s) : ℝ)
  let Nl := (Fintype.card (Fin (n+m) → G4.ShortWord w s) : ℝ)
  let I : G4.ShortWord w s := ⟨[0], (G4.mem_shortWordFamily_iff w [0]).mpr
    ⟨by simp,by simpa [wordWeight] using hw 0⟩⟩
  have hNo : 0 < No := by
    dsimp [No]
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨fun _ : Fin n => I⟩ : 0 < Fintype.card (Fin n → G4.ShortWord w s))
  have hNl : 0 < Nl := by
    dsimp [Nl]
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨fun _ : Fin (n+m) => I⟩ : 0 < Fintype.card (Fin (n+m) → G4.ShortWord w s))
  refine ⟨cl/(Co*(No/(1/2))), (Cl*(Nl/t))/co, min ro rl,
    div_pos hcl (mul_pos hCo (div_pos hNo (by norm_num))),
    div_pos (mul_pos hCl (div_pos hNl ht)) hco,lt_min hro hrl,?_⟩
  intro Ω hUΩ hUlΩ ξ hξ r hr hrr B J hB ho hl R H
  have hballo : rsBall Ω w X (basePoint ξ) r =
      {y | controlDistance Ω w X (basePoint ξ) y < ENNReal.ofReal r} :=
    ordinary_ball_inter_domain_eq Ω w X (basePoint ξ) r
  have hballl : rsBall (basePoint ⁻¹' Ω) w (triangularLift X P) ξ r =
      {y | controlDistance (basePoint ⁻¹' Ω) w (triangularLift X P) ξ y < ENNReal.ofReal r} :=
    ordinary_ball_inter_domain_eq (basePoint ⁻¹' Ω) w (triangularLift X P) ξ r
  apply completed_frame_measure_ratio_of_volumePolynomial_bounds
    (G4.shortField w X) (G4.shortField w (triangularLift X P)) (G4.shortWeight w)
    B J (basePoint ξ) ξ hr (by norm_num) ht hco hCo hcl hCl hB ho hl
    (rsBall Ω w X (basePoint ξ) r) (rsBall (basePoint ⁻¹' Ω) w (triangularLift X P) ξ r)
  · rw [hballo]
    exact hvo Ω hUΩ (basePoint ξ) ⟨ξ,hξ,rfl⟩ r hr (hrr.trans (min_le_left _ _))
  · rw [hballl]
    exact hvl (basePoint ⁻¹' Ω) hUlΩ ξ hξ r hr (hrr.trans (min_le_right _ _))

end RothschildStein.L1
