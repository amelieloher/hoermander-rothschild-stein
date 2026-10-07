-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.FirstNondegeneracy
public import RothschildStein.Definitions.sumSquaresWithDrift

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

@[expose] public section
noncomputable section
namespace RothschildStein.H1
open scoped BigOperators
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- The first derivative of the quadratic coordinate barrier (BB p. 257). -/
theorem fieldDerivative_square_coordinate
    (V : (Fin N → ℝ) → (Fin N → ℝ)) (j : Fin N) (x : Fin N → ℝ) :
    fieldDerivative V (fun y => (y j) ^ 2) x = 2 * x j * V x j := by
  unfold fieldDerivative
  rw [((hasFDerivAt_apply j x).pow 2).fderiv]
  simp

/-- The field square on xⱼ² is twice its constant coefficient squared (BB p. 257). -/
theorem fieldSquare_square_coordinate
    (V : (Fin N → ℝ) → (Fin N → ℝ)) (j : Fin N) (b : ℝ)
    (hb : ∀ y, V y j = b) (x : Fin N → ℝ) :
    fieldDerivative V (fieldDerivative V (fun y => (y j) ^ 2)) x = 2 * b ^ 2 := by
  have he : fieldDerivative V (fun y => (y j) ^ 2) = fun y => (2 * b) * y j := by
    funext y
    rw [fieldDerivative_square_coordinate, hb]
    ring
  rw [he]
  unfold fieldDerivative
  rw [((hasFDerivAt_apply j x).const_mul (2 * b)).fderiv]
  simp only [smul_apply, smul_eq_mul, ContinuousLinearMap.proj_apply]
  rw [hb]
  ring

/-- The standing operator sends the quadratic barrier to the positive constant 2c₀
(BB Proposition 6.9, pp. 256–257). -/
theorem StandingHypotheses.operator_square (H : StandingHypotheses G q) (x : Fin N → ℝ) :
    sumSquaresWithDrift H.fields (fun y => (y (firstIndex G)) ^ 2) x =
      2 * horizontalFirstSquareSum G H := by
  unfold sumSquaresWithDrift
  rw [fieldDerivative_square_coordinate, H.drift_first_zero]
  simp only [mul_zero, zero_add]
  simp_rw [fieldSquare_square_coordinate _ _ _ (H.horizontal_first_constant G _) x]
  exact (Finset.mul_sum _ _ _).symm

end RothschildStein.H1
