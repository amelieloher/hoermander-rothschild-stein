-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import Mathlib
public import RothschildStein.Definitions.bracketStepOn
public import RothschildStein.Definitions.controlDistance
public import RothschildStein.Definitions.rsBall
public import RothschildStein.Definitions.wordBracket
public import RothschildStein.Definitions.wordWeight
public import RothschildStein.Definitions.wordFamily
public import RothschildStein.Geometry.CompactFamilyDomainLocalization
public import RothschildStein.Geometry.WordFamilyVolumePolynomial
public import RothschildStein.G4.CompactParameterPairedBallVolume
public import RothschildStein.G4.VolumeDoubling
public import RothschildStein.G4.ControlTopology
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace RothschildStein.Geometry

theorem exists_ball_volume_doubling_compact_family
    {Sg : Type*} [UniformSpace Sg] [CompactSpace Sg]
    {k n s : ℕ} (hn : 0 < n)
    (w : Fin (k + 1) → ℕ+) (hw : ∀ i, (w i : ℕ) ≤ s)
    {Ω V K : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (hV : IsOpen V)
    (hK : IsCompact K) (hKV : K ⊆ V) (hVΩ : V ⊆ Ω)
    (X : Sg → Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ σ i, ContDiffOn ℝ (⊤ : ℕ∞) (X σ i) Ω)
    (hjoint : ∀ i j, ContinuousOn
      (fun z : Sg × (Fin n → ℝ) => iteratedFDeriv ℝ j (X z.1 i) z.2) (univ ×ˢ Ω))
    (hstep : ∀ σ, bracketStepOn V w (X σ) s) :
    ∃ c C L r₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < L ∧ 0 < r₀ ∧
      ∀ σ, ∀ x ∈ K,
      (∀ r : ℝ, 0 < r → r ≤ r₀ →
        let Λ : ℝ := ∑ B ∈ Fintype.piFinset (fun _ : Fin n => wordFamily w s),
          |(Matrix.of fun i j => wordBracket (X σ) (B j) x i).det| *
            r ^ (∑ j, wordWeight w (B j))
        0 < Λ ∧
        ENNReal.ofReal (c * Λ) ≤ volume (rsBall Ω w (X σ) x r) ∧
        volume (rsBall Ω w (X σ) x r) ≤ ENNReal.ofReal (C * Λ)) ∧
      (∀ A r : ℝ, 1 ≤ A → 0 < r → A * r ≤ r₀ →
        volume (rsBall Ω w (X σ) x (A * r)) ≤
          ENNReal.ofReal (L * A ^ (n * s)) * volume (rsBall Ω w (X σ) x r)) := by
  classical
  have hVopen : IsOpen V := by
    simpa only [Set.inter_eq_left.mpr hVΩ] using hV.inter hΩ
  have hs : 0 < s := lt_of_lt_of_le (w 0).pos (hw 0)
  obtain ⟨c,C,ε,hc,hC,hε,hvol⟩ := G4.exists_compact_parameter_paired_ball_volume_provider
    hn hs w hw hVopen X (fun σ i => (hX σ i).mono hVΩ) hstep
    (fun i j => (hjoint i j).mono (fun q hq => ⟨hq.1,hVΩ hq.2⟩)) K hK hKV
  obtain ⟨εo,hεo,heq⟩ := exists_compact_family_rsBall_domain_localization hK hV hKV hVΩ w X
    (fun i => G4.spatial_jet_zero_continuity_values (fun σ => X σ i) (hjoint i 0))
  refine ⟨c,C,C/c,min ε εo,hc,hC,div_pos hC hc,lt_min hε hεo,?_⟩
  intro σ x hx
  let lam := fun B : Fin n → G4.ShortWord w s => G4.frameDet (G4.shortField w (X σ)) B x
  let weights := fun B : Fin n → G4.ShortWord w s => ∑ i, (G4.shortWeight w (B i) : ℕ)
  have hv : ∀ r, 0 < r → r ≤ min ε εo →
      ENNReal.ofReal (c * G4.volumePolynomial lam weights r) ≤ volume (rsBall Ω w (X σ) x r) ∧
      volume (rsBall Ω w (X σ) x r) ≤ ENNReal.ofReal (C * G4.volumePolynomial lam weights r) := by
    intro r hr hrr
    have hh := (hvol σ x hx r hr (hrr.trans (min_le_left _ _))).1
    rw [enumerated_volumePolynomial_eq] at hh
    have hb : G4.controlBall V w (X σ) x r = rsBall V w (X σ) x r := by
      ext y
      exact ⟨fun hy => ⟨G4.controlBall_subset_domain V w (X σ) x r hy,hy⟩,fun hy => hy.2⟩
    rw [hb,← heq σ x hx r hr (hrr.trans (min_le_right _ _))] at hh
    exact hh
  constructor
  · intro r hr hrr Λ
    have hp : Λ = G4.volumePolynomial lam weights r := wordFamily_volumePolynomial_eq w (X σ) x r
    rw [hp]
    obtain ⟨B,hB⟩ := G4.exists_short_frame (hstep σ) (hKV hx)
    exact ⟨G4.volumePolynomial_pos lam weights hr B hB,(hv r hr hrr).1,(hv r hr hrr).2⟩
  · intro A r hA hr hAr
    have hwf : ∀ B : Fin n → G4.ShortWord w s, weights B ≤ n*s := by
      intro B
      have h := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) =>
        ((G4.mem_shortWordFamily_iff w (B j).val).mp (B j).property).2)
      change (∑ j, wordWeight w (B j).val) ≤ n*s
      simpa only [Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul, mul_comm] using h
    exact G4.measure_scale_le_of_volumePolynomial_bounds volume
      (fun t => rsBall Ω w (X σ) x t) lam weights hwf hc hC.le hv hA hr hAr
end RothschildStein.Geometry
