-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.OperatorWordSum
public import RothschildStein.Definitions.driftWeight

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open MeasureTheory
open scoped ENNReal BigOperators

/-- The drift norm follows from the diagonal horizontal estimates and
the literal fixed operator identity, with coefficient one plus qC. -/
theorem drift_word_norm_le_of_horizontal_squares {n q : ℕ}
    (X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ)) (u : (Fin n → ℝ) → ℝ)
    (p : ℝ≥0∞) (hp : 1 ≤ p) {C : ℝ} (hC : 0 ≤ C)
    (hdiag : ∀ i : Fin q, eLpNorm (wordDerivative X [i.succ,i.succ] u) p volume ≤
      ENNReal.ofReal C * eLpNorm (sumSquaresWithDrift X u) p volume) :
    eLpNorm (wordDerivative X [0] u) p volume ≤
      ENNReal.ofReal (1+(q : ℝ)*C) * eLpNorm (sumSquaresWithDrift X u) p volume := by
  have he : wordDerivative X [0] u = sumSquaresWithDrift X u -
      ∑ i : Fin q, wordDerivative X [i.succ,i.succ] u := by
    rw [sumSquaresWithDrift_eq_word_sum]
    simp
  rw [he]
  have hs := eLpNorm_sum_le (μ := volume) (f := fun i : Fin q => wordDerivative X [i.succ,i.succ] u)
    (s := Finset.univ) hp
  calc
    eLpNorm (sumSquaresWithDrift X u - ∑ i : Fin q, wordDerivative X [i.succ,i.succ] u) p volume
      ≤ eLpNorm (sumSquaresWithDrift X u) p volume +
        eLpNorm (∑ i : Fin q, wordDerivative X [i.succ,i.succ] u) p volume := eLpNorm_sub_le hp
    _ ≤ eLpNorm (sumSquaresWithDrift X u) p volume +
        ∑ i : Fin q, eLpNorm (wordDerivative X [i.succ,i.succ] u) p volume := add_le_add le_rfl hs
    _ ≤ eLpNorm (sumSquaresWithDrift X u) p volume +
        ∑ _i : Fin q, ENNReal.ofReal C*eLpNorm (sumSquaresWithDrift X u) p volume :=
      add_le_add le_rfl (Finset.sum_le_sum (fun i _ => hdiag i))
    _ = ENNReal.ofReal (1+(q : ℝ)*C)*eLpNorm (sumSquaresWithDrift X u) p volume := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by positivity)]
      simp only [ENNReal.ofReal_one, ENNReal.ofReal_natCast, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

end RothschildStein.H3
