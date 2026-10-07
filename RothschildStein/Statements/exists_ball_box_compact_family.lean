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
public import RothschildStein.Provider.exists_ball_box_compact_family

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace RothschildStein

/-- The ball-box theorem, uniform over a compact parameter family, with the
bracket step on a buffer `V ⊇ K` and balls in `Ω` (BB Thm 9.11; NSW Acta 155 Thm 7): for every θ-suboptimal frame the
exponential chart is smooth and injective on the weighted box, with Jacobian comparable to the frame determinant, and
its image lies between two control balls. -/
theorem exists_ball_box_compact_family
    {Sg : Type*} [UniformSpace Sg] [CompactSpace Sg]
    {k n s : ℕ} (hn : 0 < n)
    (w : Fin (k + 1) → ℕ+) (hw : ∀ i, (w i : ℕ) ≤ s)
    {Ω V K : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (hV : IsOpen V)
    (hK : IsCompact K) (hKV : K ⊆ V) (hVΩ : V ⊆ Ω)
    (X : Sg → Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ σ i, ContDiffOn ℝ (⊤ : ℕ∞) (X σ i) Ω)
    (hjoint : ∀ i j, ContinuousOn
      (fun z : Sg × (Fin n → ℝ) => iteratedFDeriv ℝ j (X z.1 i) z.2) (univ ×ˢ Ω))
    (hstep : ∀ σ, bracketStepOn V w (X σ) s)
    (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1) :
    ∃ a b C r₀ : ℝ, 0 < a ∧ 0 < b ∧ 0 < C ∧ 0 < r₀ ∧
      ∀ σ, ∀ x ∈ K, ∀ r : ℝ, 0 < r → r ≤ r₀ →
      ∀ B : Fin n → List (Fin (k + 1)), (∀ j, wordWeight w (B j) ≤ s) →
      (∀ B' : Fin n → List (Fin (k + 1)), (∀ j, wordWeight w (B' j) ≤ s) →
        θ * (|(Matrix.of fun i j => wordBracket (X σ) (B' j) x i).det| *
              r ^ (∑ j, wordWeight w (B' j))) ≤
          |(Matrix.of fun i j => wordBracket (X σ) (B j) x i).det| *
            r ^ (∑ j, wordWeight w (B j))) →
      let Q : Set (Fin n → ℝ) := {u | ∀ j, |u j| < (a * r) ^ wordWeight w (B j)}
      let lam : ℝ := (Matrix.of fun i j => wordBracket (X σ) (B j) x i).det
      ∃ F : (Fin n → ℝ) → (Fin n → ℝ),
        (∀ u ∈ Q, ∃ γ : ℝ → (Fin n → ℝ), γ 0 = x ∧ γ 1 = F u ∧
          ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ Ω ∧
            HasDerivWithinAt γ (∑ j, u j • wordBracket (X σ) (B j) (γ t)) (Icc 0 1) t) ∧
        ContDiffOn ℝ (⊤ : ℕ∞) F Q ∧ InjOn F Q ∧
        (∀ u ∈ Q, |lam| / 4 ≤ absoluteJacobian F u ∧ absoluteJacobian F u ≤ 4 * |lam|) ∧
        rsBall Ω w (X σ) x (b * r) ⊆ F '' Q ∧
        F '' Q ⊆ rsBall Ω w (X σ) x (C * r) :=
  by exact RothschildStein.Provider.exists_ball_box_compact_family hn w hw hΩ hV hK hKV hVΩ X hX hjoint hstep θ hθ hθ1

end RothschildStein
