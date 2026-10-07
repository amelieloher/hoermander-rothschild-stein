-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.DriftWeightTwoCases
public import RothschildStein.H3.DriftWordNormBound

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open MeasureTheory
open scoped ENNReal

/-- all ordered horizontal estimates supply the exact
complete weight-two estimate, including drift, with one positive constant. -/
theorem compact_weight_two_estimate_of_horizontal_bounds {n q : ℕ}
    (X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (p : ℝ≥0∞) (hp : 1 ≤ p) {C : ℝ} (hC : 0 ≤ C)
    (hhor : ∀ u : (Fin n → ℝ) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) u → HasCompactSupport u → ∀ i j : Fin q,
        eLpNorm (wordDerivative X [i.succ,j.succ] u) p volume ≤
          ENNReal.ofReal C*eLpNorm (sumSquaresWithDrift X u) p volume) :
    0 < (q+1 : ℝ)*(C+1) ∧
      ∀ u : (Fin n → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) u → HasCompactSupport u →
        ∀ I : List (Fin (q+1)), wordWeight driftWeight I = 2 →
          eLpNorm (wordDerivative X I u) p volume ≤
            ENNReal.ofReal ((q+1 : ℝ)*(C+1))*eLpNorm (sumSquaresWithDrift X u) p volume := by
  have hq : 0 ≤ (q : ℝ) := Nat.cast_nonneg _
  refine ⟨by positivity,?_⟩
  intro u hu hc I hI
  rcases drift_word_weight_two I hI with hz | ⟨i,j,hij⟩
  · subst I
    apply (drift_word_norm_le_of_horizontal_squares X u p hp hC
      (fun i => hhor u hu hc i i)).trans
    apply mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    nlinarith
  · subst I
    apply (hhor u hu hc i j).trans
    apply mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    nlinarith

end RothschildStein.H3
