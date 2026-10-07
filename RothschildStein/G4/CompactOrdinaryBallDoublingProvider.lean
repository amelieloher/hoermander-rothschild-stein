-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.CompactOrdinaryBallVolumeProvider

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace RothschildStein.G4

/-- Actual ordinary balls have compact-center uniform positive
finite volume and local fixed-factor doubling. All constants are supplied
by the smooth bracket-generating system and local comparison of the Euclidean and control topologies (BB Theorem 9.1, p. 400). -/
theorem exists_compact_ordinary_ball_doubling_provider_of_local_comparison {k n s : ℕ}
    (hn : 0 < n) (hs : 1 ≤ s) (w : Fin (k + 1) → ℕ+)
    (D : G3.FreeModelData (k+1) s w) (hweights : ∀ i, (w i : ℕ) ≤ s)
    {Ω K : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (X : Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hstep : bracketStepOn Ω w X s)
    (hcomparison : G1.LocalControlComparison Ω w X s) :
    ∃ L ε : ℝ, 0 < L ∧ 0 < ε ∧ ∀ x ∈ K,
      (∀ r, 0 < r → r ≤ ε →
        0 < volume {y | controlDistance Ω w X x y < ENNReal.ofReal r} ∧
        volume {y | controlDistance Ω w X x y < ENNReal.ofReal r} < ∞) ∧
      (∀ A r, 1 ≤ A → 0 < r → A * r ≤ ε →
        volume {y | controlDistance Ω w X x y < ENNReal.ofReal (A * r)} ≤
          ENNReal.ofReal (L * A ^ (n * s)) *
            volume {y | controlDistance Ω w X x y < ENNReal.ofReal r}) := by
  obtain ⟨c, C, ε, hc, hC, hε, hvol⟩ :=
    exists_compact_ordinary_ball_volume_provider_of_local_comparison hn hs w D hweights hΩ hK hKΩ X hX hstep hcomparison
  refine ⟨C / c, ε, div_pos hC hc, hε, ?_⟩
  intro x hx
  let lam : (Fin n → ShortWord w s) → ℝ := fun B => frameDet (shortField w X) B x
  let weights : (Fin n → ShortWord w s) → ℕ := fun B => ∑ i, (shortWeight w (B i) : ℕ)
  have hw : ∀ B, weights B ≤ n * s := fun B =>
    frame_natural_weight_le (shortWeight w)
      (fun I => ((mem_shortWordFamily_iff w I.val).mp I.property).2) B
  obtain ⟨B, hB⟩ := exists_short_frame hstep (hKΩ hx)
  constructor
  · intro r hr hrr
    obtain ⟨hlo, hhi⟩ := hvol x hx r hr hrr
    exact measure_pos_finite_of_volumePolynomial_bounds volume _ lam weights hc hr B hB hlo hhi
  · intro A r hA hr hAr
    exact measure_scale_le_of_volumePolynomial_bounds volume
      (fun r => {y | controlDistance Ω w X x y < ENNReal.ofReal r})
      lam weights hw hc hC.le (hvol x hx) hA hr hAr

end RothschildStein.G4
