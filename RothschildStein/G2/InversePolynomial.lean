-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.TriangularPolynomial
public import RothschildStein.G2.TriangularMeasure

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
namespace RothschildStein.G2
open MvPolynomial
variable {N : ℕ} (G : HomogeneousGroup N)

/-- The inverse coordinate correction (BB Proposition 3.7, p. 98). -/
def inverseCorrection (k : Fin N) : MvPolynomial (Fin N) ℝ := G.inversePolynomial k + X k

/-- The inverse has additive leading part −x (BB Proposition 3.7, p. 98). -/
theorem inv_coordinate (x : Fin N → ℝ) (k : Fin N) :
    G.inv x k = -x k + eval x (inverseCorrection G k) := by
  simp [inverseCorrection, HomogeneousGroup.inv]

/-- Coordinate recursion for inversion (BB Proposition 3.7, p. 98). -/
theorem inv_coordinate_recursion (x : Fin N → ℝ) (k : Fin N) :
    G.inv x k = -x k - eval (Sum.elim x (G.inv x)) (correction G k) := by
  have h := mul_coordinate G x (G.inv x) k
  rw [mul_inv] at h
  change 0 = _ at h
  linarith

/-- An inverse coordinate is determined by input coordinates up to its index
(BB Proposition 3.7, p. 98). -/
theorem inv_coordinate_congr (k : Fin N) {x y : Fin N → ℝ}
    (hxy : ∀ j, j ≤ k → x j = y j) : G.inv x k = G.inv y k := by
  induction k using WellFoundedLT.induction with
  | ind k ih =>
    rw [inv_coordinate_recursion G x k, inv_coordinate_recursion G y k, hxy k le_rfl]
    congr 1
    apply correction_eval_congr G k
    · intro j hj
      exact hxy j (le_of_lt hj)
    · intro j hj
      exact ih j hj (fun i hi => hxy i (hi.trans (le_of_lt hj)))

/-- The inverse correction depends only on strictly earlier coordinates
(BB Proposition 3.7, p. 98). -/
theorem inverseCorrection_eval_congr (k : Fin N) {x y : Fin N → ℝ}
    (hxy : ∀ j, j < k → x j = y j) :
    eval x (inverseCorrection G k) = eval y (inverseCorrection G k) := by
  have hc := correction_eval_congr G k hxy (fun j hj =>
    inv_coordinate_congr G j (fun i hi => hxy i (lt_of_le_of_lt hi hj)))
  have hx := inv_coordinate G x k
  have hy := inv_coordinate G y k
  rw [inv_coordinate_recursion G x k] at hx
  rw [inv_coordinate_recursion G y k] at hy
  linarith

/-- Inversion is signed triangular (BB Proposition 3.7, p. 98). -/
theorem inv_isTriangular : IsTriangular G.inv (fun _ => -1) := by
  intro k x y hxy
  have h := inverseCorrection_eval_congr G k hxy
  rw [inv_coordinate G x k, inv_coordinate G y k]
  linarith

end RothschildStein.G2
