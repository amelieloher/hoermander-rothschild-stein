-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.WordPolynomialExponential
public import RothschildStein.G3.Homogeneity
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- Powers of an ordinary homogeneous linear word polynomial have
exactly the corresponding ordinary operator-factor count (BB pp. 413–414). -/
theorem polynomialSeries_power_homogeneous {a : ℕ}
    (P : MonoidAlgebra ℝ (FreeMonoid (Fin a)))
    (hP : Homogeneous (fun _ : Fin a => 1) 1 (polynomialSeries a P)) (k : ℕ) :
    Homogeneous (fun _ : Fin a => 1) k ((polynomialSeries a P) ^ k) := by
  induction k with
  | zero =>
    intro J hJ
    rw [pow_zero]
    change (if J = [] then (1 : ℝ) else 0) = 0
    have hne : J ≠ [] := by intro he; subst J; simp [wordWeight] at hJ
    exact ite_eq_right hne
  | succ k ih =>
    rw [pow_succ]
    exact homogeneous_convolution (fun _ => 1) ih hP

/-- Exponential polynomials of a linear bracket-field input contain
at most n field factors, independently of the bracket fields' weights. -/
theorem wordPolynomialExp_coeff_eq_zero_of_length_gt {a n : ℕ}
    (P : MonoidAlgebra ℝ (FreeMonoid (Fin a)))
    (hP : Homogeneous (fun _ : Fin a => 1) 1 (polynomialSeries a P))
    (I : List (Fin a)) (hI : n < I.length) :
    polynomialSeries a (wordPolynomialExp P n) I = 0 := by
  rw [wordPolynomialExp, map_sum]
  simp only [map_smul]
  change seriesCoefficientLinear I
    (∑ k ∈ Finset.range (n + 1), (k.factorial : ℝ)⁻¹ • (polynomialSeries a (P ^ k))) = 0
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro k hk
  change (k.factorial : ℝ)⁻¹ * polynomialSeries a (P ^ k) I = 0
  rw [map_pow, polynomialSeries_power_homogeneous P hP k I
    (by rw [ordinary_weight]; have hh := Finset.mem_range.mp hk; omega), mul_zero]

/-- A uniform letter-weight bound controls the weight of each word. -/
theorem wordWeight_le_bound_mul_length {a : ℕ} (q : Fin a → ℕ+) (Q : ℕ)
    (hq : ∀ i, (q i : ℕ) ≤ Q) (I : List (Fin a)) :
    wordWeight q I ≤ Q * I.length := by
  induction I with
  | nil => simp [wordWeight]
  | cons i I ih =>
    simp only [wordWeight, List.map_cons, List.sum_cons, List.length_cons, Nat.mul_add, Nat.mul_one]
    have hi := hq i
    change (q i : ℕ) + wordWeight q I ≤ Q * I.length + Q
    omega

end RothschildStein.G3
