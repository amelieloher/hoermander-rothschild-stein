-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.FirstNondegeneracy
public import RothschildStein.Definitions.sumSquaresWithDrift
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

@[expose] public section
noncomputable section
namespace RothschildStein.H1
open scoped BigOperators
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- Directional differentiation of the exponential coordinate barrier (BB p. 257). -/
theorem fieldDerivative_exp_coordinate
    (V : (Fin N → ℝ) → (Fin N → ℝ)) (j : Fin N) (γ : ℝ) (x : Fin N → ℝ) :
    fieldDerivative V (fun y => Real.exp (γ * y j)) x = γ * V x j * Real.exp (γ * x j) := by
  unfold fieldDerivative
  rw [(((hasFDerivAt_apply j x).const_mul γ).exp).fderiv]
  simp only [smul_apply, smul_eq_mul, ContinuousLinearMap.proj_apply]
  ring

/-- The square of a field with constant first coefficient acts on the barrier by γ²b²
(BB p. 257). -/
theorem fieldSquare_exp_coordinate
    (V : (Fin N → ℝ) → (Fin N → ℝ)) (j : Fin N) (b γ : ℝ)
    (hb : ∀ y, V y j = b) (x : Fin N → ℝ) :
    fieldDerivative V (fieldDerivative V (fun y => Real.exp (γ * y j))) x =
      γ ^ 2 * b ^ 2 * Real.exp (γ * x j) := by
  have he : fieldDerivative V (fun y => Real.exp (γ * y j)) =
      fun y => (γ * b) * Real.exp (γ * y j) := by
    funext y
    rw [fieldDerivative_exp_coordinate, hb]
  rw [he]
  unfold fieldDerivative
  rw [((((hasFDerivAt_apply j x).const_mul γ).exp).const_mul (γ * b)).fderiv]
  simp only [smul_apply, smul_eq_mul, ContinuousLinearMap.proj_apply]
  rw [hb]
  ring

/-- The standing operator acts on every exponential coordinate barrier by γ²c₀
(BB Proposition 6.9, pp. 256–257). -/
theorem StandingHypotheses.operator_exp (H : StandingHypotheses G q)
    (γ : ℝ) (x : Fin N → ℝ) :
    sumSquaresWithDrift H.fields (fun y => Real.exp (γ * y (firstIndex G))) x =
      γ ^ 2 * horizontalFirstSquareSum G H * Real.exp (γ * x (firstIndex G)) := by
  unfold sumSquaresWithDrift
  rw [fieldDerivative_exp_coordinate, H.drift_first_zero]
  simp only [mul_zero, zero_mul, zero_add]
  simp_rw [fieldSquare_exp_coordinate _ _ _ _ (H.horizontal_first_constant G _) x]
  unfold horizontalFirstSquareSum
  rw [Finset.mul_sum, Finset.sum_mul]

/-- The normalized exponential barrier is an eigenfunction with eigenvalue one
(BB p. 257; c₀ positivity is proved from bracket span). -/
theorem StandingHypotheses.operator_normalized_exp (H : StandingHypotheses G q)
    (x : Fin N → ℝ) :
    sumSquaresWithDrift H.fields
      (fun y => Real.exp ((Real.sqrt (horizontalFirstSquareSum G H))⁻¹ * y (firstIndex G))) x =
      Real.exp ((Real.sqrt (horizontalFirstSquareSum G H))⁻¹ * x (firstIndex G)) := by
  rw [H.operator_exp G]
  have hp := H.horizontalFirstSquareSum_pos G
  have hs := Real.sq_sqrt hp.le
  have he : (Real.sqrt (horizontalFirstSquareSum G H))⁻¹ ^ 2 * horizontalFirstSquareSum G H = 1 := by
    rw [inv_pow, hs, inv_mul_cancel₀ hp.ne']
  rw [he, one_mul]

end RothschildStein.H1
