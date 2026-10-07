-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.AmbientOrdinaryVolumeProvider
public import RothschildStein.G1.ActualControlComparison
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators
namespace RothschildStein.L1

/-- The actual original ambient volume polynomial bounds follow
from smooth bracket generation on a local patch. This discharges the
G1 comparison input used in the completed-frame ratio (BB pp. 521–522). -/
theorem exists_compact_ambient_ordinary_volume_provider {k n s : ℕ}
    (hn : 0 < n) (hs : 1 ≤ s) (w : Fin (k+1) → ℕ+) (hweights : ∀ i, (w i : ℕ) ≤ s)
    {U K : Set (Fin n → ℝ)} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (X : Fin (k+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) U)
    (hstep : bracketStepOn U w X s) :
    ∃ c C ε : ℝ, 0 < c ∧ 0 < C ∧ 0 < ε ∧
      ∀ Ω : Set (Fin n → ℝ), U ⊆ Ω → ∀ x ∈ K, ∀ r, 0 < r → r ≤ ε →
        let Λ := G4.volumePolynomial
          (fun B : Fin n → G4.ShortWord w s => G4.frameDet (G4.shortField w X) B x)
          (fun B => ∑ i, (G4.shortWeight w (B i) : ℕ)) r
        ENNReal.ofReal (c*Λ) ≤ volume {y | controlDistance Ω w X x y < ENNReal.ofReal r} ∧
        volume {y | controlDistance Ω w X x y < ENNReal.ofReal r} ≤ ENNReal.ofReal (C*Λ) := by
  exact exists_compact_ambient_ordinary_volume_provider_of_local_comparison hn hs w hweights
    hU hK hKU X hX hstep
    (G1.localControlComparison_of_smooth_bracketStep hU w X hX hs hweights hstep)

end RothschildStein.L1
