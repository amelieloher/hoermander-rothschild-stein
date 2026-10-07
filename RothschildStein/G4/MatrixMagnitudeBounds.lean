-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.GlobalReduction
public import Mathlib.Data.Int.AbsoluteValue

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

/-- The determinant polynomial has a universal bound in terms
of dimension and a common coordinate bound (BB Lemma 9.31, pp. 422–423). -/
theorem abs_det_le_factorial_pow {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    {H : ℝ} (_hH : 0 ≤ H) (hA : ∀ i j, |A i j| ≤ H) :
    |A.det| ≤ (n.factorial : ℝ) * H ^ n := by
  classical
  rw [Matrix.det_apply']
  have hsign : ∀ σ : Equiv.Perm (Fin n), |((Equiv.Perm.sign σ : ℤ) : ℝ)| = 1 := by
    intro σ
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;> simp
  calc
    _ ≤ ∑ σ : Equiv.Perm (Fin n), |((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ j, A (σ j) j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin n), H ^ n := by
      apply Finset.sum_le_sum
      intro σ hσ
      rw [abs_mul, hsign σ, one_mul, Finset.abs_prod]
      have hh := Finset.prod_le_prod₀ (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => abs_nonneg (A (σ j) j))
        (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => hA (σ j) j)
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hh
    _ = _ := by simp [Fintype.card_perm]

/-- Replacing one column retains an explicit determinant-polynomial
bound, including dimension zero (BB Lemma 9.31, pp. 422–423). -/
theorem replacementDet_le_factorial_pow {ι : Type*} {n : ℕ}
    (Z : ι → (Fin n → ℝ) → (Fin n → ℝ)) (B : Fin n → ι)
    (v : Fin n → ℝ) (j : Fin n) (x : Fin n → ℝ)
    {H : ℝ} (hH : 0 ≤ H) (hZ : ∀ J k, |Z J x k| ≤ H) (hv : ∀ k, |v k| ≤ H) :
    |replacementDet Z B v j x| ≤ (n.factorial : ℝ) * H ^ n := by
  apply abs_det_le_factorial_pow _ hH
  intro k i
  by_cases hi : i = j
  · subst i
    simpa only [Matrix.updateCol_self] using hv k
  · simpa only [Matrix.updateCol_ne hi, frameMatrix] using hZ (B i) k

end RothschildStein.G4
