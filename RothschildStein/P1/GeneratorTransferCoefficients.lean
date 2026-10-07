-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.InputBracketApproximation
public import RothschildStein.G2.WeightSpaces
public import Mathlib.Algebra.BigOperators.Pi

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MvPolynomial
open scoped BigOperators
namespace RothschildStein.P1.LiftedChart
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  (C : LiftedChart w s Ω hΩ X x₀ m)

/-- Polynomial coefficients expressing a model generator in
the canonical right invariant basis. -/
def generatorTransferCoefficient (i : Fin k) (j : Fin (n + m)) :
    MvPolynomial (Fin (n + m)) ℝ :=
  ∑ l, C.v i l • G2.leftRightChangeMatrix C.G l j

/-- A generator vector has coordinates only in its own weight space. -/
theorem generator_coordinate_zero_of_weight_ne (i : Fin k) (j : Fin (n + m))
    (hj : C.G.weight j ≠ (w i : ℕ)) : C.v i j = 0 := by
  have hh := C.isHomogeneousField i
  rw [C.model_field_eq_leftField i] at hh
  exact (G2.leftField_homogeneous_iff C.G (C.v i) ((w i : ℕ) : ℝ)).mp hh j
    (by exact_mod_cast hj)

/-- The transfer coefficient has exactly the difference of weights. -/
theorem generatorTransferCoefficient_eval_dilate (i : Fin k) (j : Fin (n + m))
    (t : ℝ) (ht : 0 < t) (u : Fin (n + m) → ℝ) :
    eval (C.G.dilate t u) (C.generatorTransferCoefficient i j) =
      t ^ ((C.G.weight j : ℝ) - (w i : ℕ)) *
        eval u (C.generatorTransferCoefficient i j) := by
  classical
  simp only [generatorTransferCoefficient, map_sum, smul_eq_C_mul, map_mul, eval_C, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  by_cases hl : C.G.weight l = (w i : ℕ)
  · rw [G2.leftRightChangeMatrix_eval_dilate C.G l j t ht u, hl]
    ring
  · rw [C.generator_coordinate_zero_of_weight_ne i l hl]
    simp only [mul_zero, zero_mul]

/-- No smaller-weight basis bracket occurs in generator transfer. -/
theorem generatorTransferCoefficient_zero_of_weight_lt (i : Fin k) (j : Fin (n + m))
    (hj : C.G.weight j < (w i : ℕ)) : C.generatorTransferCoefficient i j = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro l _
  by_cases hl : C.G.weight l = (w i : ℕ)
  · rw [G2.leftRightChangeMatrix_zero_of_weight_lt C.G l j (by omega), smul_zero]
  · rw [C.generator_coordinate_zero_of_weight_ne i l hl, zero_smul]

/-- Actual polynomial expansion of the model generator in the right basis. -/
theorem generator_right_expansion (i : Fin k) (u : Fin (n + m) → ℝ) :
    C.Y i u = ∑ j, eval u (C.generatorTransferCoefficient i j) •
      G2.rightField C.G (Pi.single j 1) u := by
  classical
  rw [C.model_field_eq i u]
  conv_lhs => arg 2; rw [pi_eq_sum_univ' (C.v i)]
  simp only [map_sum, map_smul]
  change (∑ l, C.v i l • C.G.canonicalField l u) = _
  simp_rw [G2.canonicalField_right_expansion]
  simp only [Finset.smul_sum, smul_smul, generatorTransferCoefficient, map_sum,
    smul_eq_C_mul, map_mul, eval_C, Finset.sum_smul, Hormander.Interface.basisVec]
  rw [Finset.sum_comm]

/-- Transfer of a generator to actual input basis brackets,
with the entire reflected remainder retained as a separate error field. -/
theorem generator_input_transfer (i : Fin k)
    {ξ η : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U) (hη : η ∈ C.U) :
    C.Y i (C.Θ η ξ) =
      -(∑ j, eval (C.Θ η ξ) (C.generatorTransferCoefficient i j) •
        fderiv ℝ (fun ζ => C.Θ ζ ξ) η (wordBracket C.Xl (C.B j) η)) -
      ∑ j, eval (C.Θ η ξ) (C.generatorTransferCoefficient i j) •
        C.R (C.B j) ξ (-C.Θ η ξ) := by
  rw [C.generator_right_expansion]
  have he (j : Fin (n + m)) : G2.rightField C.G (Pi.single j 1) (C.Θ η ξ) =
      -fderiv ℝ (fun ζ => C.Θ ζ ξ) η (wordBracket C.Xl (C.B j) η) -
        C.R (C.B j) ξ (-C.Θ η ξ) := by
    rw [C.inputBasis_approx j hξ hη]
    abel
  simp_rw [he, smul_sub, smul_neg]
  rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib]

end RothschildStein.P1.LiftedChart
