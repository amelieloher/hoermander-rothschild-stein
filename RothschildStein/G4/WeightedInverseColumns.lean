-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.MatrixInverseBound
public import Mathlib.Algebra.BigOperators.Field

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators

namespace RothschildStein.G4

/-- Every inverse column of an identity-plus-weighted-error
matrix has the source weight orientation. Diagonal normalization gives
the proved 4/3 inverse norm bound (BB Lemma 9.51, pp. 446–447). -/
theorem weighted_identity_add_inverse_column_bound {n : ℕ}
    (w : Fin n → ℕ) (E : Matrix (Fin n) (Fin n) ℝ) {r κ : ℝ}
    (hr : 0 < r) (hκ : 0 ≤ κ) (hsmall : (n : ℝ) * κ ≤ 1 / 4)
    (hE : ∀ i j, |E i j| ≤ κ * r ^ w i / r ^ w j)
    (u : Fin n → ℝ) (ℓ : Fin n) (hsol : (1 + E).mulVec u = Pi.single ℓ 1) :
    ∀ i, |u i| ≤ (4 / 3 : ℝ) * r ^ w i / r ^ w ℓ := by
  classical
  let N : Matrix (Fin n) (Fin n) ℝ := fun i j => E i j * r ^ w j / r ^ w i
  let v : Fin n → ℝ := fun i => u i / r ^ w i
  let b : Fin n → ℝ := Pi.single ℓ (1 / r ^ w ℓ)
  have hd : ∀ i, r ^ w i ≠ 0 := fun i => ne_of_gt (pow_pos hr _)
  have hN := weightedMatrix_entry_bound w E hr hE
  obtain ⟨L, hL, hLnorm⟩ := identity_add_matrixOperator_inverse N hκ hN hsmall
  have hLv : L v = b := by
    change (L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) v = b
    rw [hL]
    ext i
    change u i / r ^ w i + ∑ j, (E i j * r ^ w j / r ^ w i) * (u j / r ^ w j) = b i
    have hsum : (∑ j, (E i j * r ^ w j / r ^ w i) * (u j / r ^ w j)) =
        (∑ j, E i j * u j) / r ^ w i := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j hj
      field_simp [hd]
    rw [hsum, ← add_div]
    have hcoord : u i + ∑ j, E i j * u j = (Pi.single ℓ (1 : ℝ) : Fin n → ℝ) i := by
      have hh := hsol
      rw [Matrix.add_mulVec, Matrix.one_mulVec] at hh
      simpa only [Pi.add_apply, Matrix.mulVec, dotProduct] using congrFun hh i
    rw [hcoord]
    by_cases hi : i = ℓ
    · subst i; simp [b]
    · simp [b, hi]
  have hv : v = L.symm b := by rw [← hLv, L.symm_apply_apply]
  have hnorm : ‖v‖ ≤ (4 / 3 : ℝ) * (1 / r ^ w ℓ) := by
    rw [hv]
    have hb : ‖b‖ = 1 / r ^ w ℓ := by
      simp only [b, Pi.norm_single, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / r ^ w ℓ)]
    exact ((L.symm : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)).le_opNorm b).trans
      ((mul_le_mul_of_nonneg_right hLnorm (norm_nonneg b)).trans_eq (by rw [hb]))
  intro i
  have hcoord : |u i / r ^ w i| ≤ ‖v‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i
  have hi : |u i / r ^ w i| ≤ (4 / 3 : ℝ) * (1 / r ^ w ℓ) := hcoord.trans hnorm
  rw [abs_div, abs_of_pos (pow_pos hr _)] at hi
  have hh := (div_le_iff₀ (pow_pos hr _)).mp hi
  exact hh.trans_eq (by ring)

end RothschildStein.G4
