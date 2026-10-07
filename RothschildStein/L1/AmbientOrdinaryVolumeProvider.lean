-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.CompactDomainBallEquality
public import RothschildStein.G4.OrdinaryGeometryProviders
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators
namespace RothschildStein.L1

/-- Smooth bracket generation only on the coefficient patch
and the exact G1 patch topology input supply actual ordinary volume bounds for every containing ambient path domain.
First exit identifies the small balls; no ambient rank hypothesis is needed. -/
theorem exists_compact_ambient_ordinary_volume_provider_of_local_comparison {k n s : ℕ}
    (hn : 0 < n) (hs : 1 ≤ s) (w : Fin (k+1) → ℕ+) (hweights : ∀ i, (w i : ℕ) ≤ s)
    {U K : Set (Fin n → ℝ)} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (X : Fin (k+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) U)
    (hstep : bracketStepOn U w X s)
    (hcomparison : G1.LocalControlComparison U w X s) :
    ∃ c C ε : ℝ, 0 < c ∧ 0 < C ∧ 0 < ε ∧
      ∀ Ω : Set (Fin n → ℝ), U ⊆ Ω → ∀ x ∈ K, ∀ r, 0 < r → r ≤ ε →
        let Λ := G4.volumePolynomial
          (fun B : Fin n → G4.ShortWord w s => G4.frameDet (G4.shortField w X) B x)
          (fun B => ∑ i, (G4.shortWeight w (B i) : ℕ)) r
        ENNReal.ofReal (c*Λ) ≤ volume {y | controlDistance Ω w X x y < ENNReal.ofReal r} ∧
        volume {y | controlDistance Ω w X x y < ENNReal.ofReal r} ≤ ENNReal.ofReal (C*Λ) := by
  obtain ⟨c, C, ε, hc, hC, hε, hv⟩ :=
    G4.exists_compact_ordinary_volume_provider_of_local_comparison hn hs w hweights hU hK hKU X hX hstep hcomparison
  obtain ⟨ρ, hρ, _hρ1, hd⟩ := exists_compact_ball_domain_equalities (s := s) hU hK hKU X hX w
  refine ⟨c, C, min ε ρ, hc, hC, lt_min hε hρ, ?_⟩
  intro Ω hUΩ x hx r hr hrr
  rw [(hd Ω hUΩ x hx r hr (hrr.trans (min_le_right _ _))).1]
  exact hv x hx r hr (hrr.trans (min_le_left _ _))
end RothschildStein.L1
