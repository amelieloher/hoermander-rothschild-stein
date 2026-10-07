-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators

namespace RothschildStein.G4

/-- An open weighted coordinate box has Lebesgue measure
2^n r^(sum w). The zero-dimensional product also satisfies the formula
(BB proof of Thm 9.12, p. 405). -/
theorem volume_weighted_coordinate_box {n : ℕ} (w : Fin n → ℕ) {r : ℝ} (hr : 0 ≤ r) :
    volume (Set.pi Set.univ (fun i : Fin n => Ioo (-(r ^ w i)) (r ^ w i))) =
      ENNReal.ofReal ((2 : ℝ) ^ n * r ^ (∑ i, w i)) := by
  rw [Real.volume_pi_Ioo]
  have hlen : ∀ i : Fin n, r ^ w i - -(r ^ w i) = 2 * r ^ w i := fun i => by ring
  simp_rw [hlen]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => mul_nonneg (by norm_num) (pow_nonneg hr (w i))),
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Finset.prod_pow_eq_pow_sum]

end RothschildStein.G4
