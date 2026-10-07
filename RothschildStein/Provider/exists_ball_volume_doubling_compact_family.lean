-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib
public import RothschildStein.Definitions.bracketStepOn
public import RothschildStein.Definitions.controlDistance
public import RothschildStein.Definitions.rsBall
public import RothschildStein.Definitions.wordBracket
public import RothschildStein.Definitions.wordWeight
public import RothschildStein.Definitions.absoluteJacobian
public import RothschildStein.Definitions.wordFamily
public import RothschildStein.Geometry.BallVolumeDoublingCompactFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace RothschildStein.Provider

/-- Compact-family volume doubling,
proved in `RothschildStein.Geometry.exists_ball_volume_doubling_compact_family`. -/
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
          ENNReal.ofReal (L * A ^ (n * s)) * volume (rsBall Ω w (X σ) x r)) :=
  by exact RothschildStein.Geometry.exists_ball_volume_doubling_compact_family
      hn w hw hΩ hV hK hKV hVΩ X hX hjoint hstep

end RothschildStein.Provider
