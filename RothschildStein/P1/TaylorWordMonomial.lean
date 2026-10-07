-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.WeightedTaylorParameters

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators

namespace RothschildStein.P1

variable {N : ℕ}

/-- Coordinate monomial indexed by an ordered word;
repeated indices retain their multiplicity. -/
def taylorWordMonomial (J : List (Fin N)) (u : Fin N → ℝ) : ℝ := (J.map u).prod

/-- The empty coordinate monomial is one. -/
theorem taylorWordMonomial_nil (u : Fin N → ℝ) : taylorWordMonomial [] u = 1 := rfl

/-- Prepending a coordinate multiplies the monomial
by that coordinate. -/
theorem taylorWordMonomial_cons (j : Fin N) (J : List (Fin N)) (u : Fin N → ℝ) :
    taylorWordMonomial (j :: J) u = u j * taylorWordMonomial J u := rfl

/-- Each finite coordinate monomial is smooth. -/
theorem taylorWordMonomial_contDiff (J : List (Fin N)) :
    ContDiff ℝ (⊤ : ℕ∞) (taylorWordMonomial J) := by
  induction J with
  | nil => exact contDiff_const
  | cons j J ih => exact (contDiff_apply ℝ ℝ j).mul ih

/-- The monomial degree is exactly the sum of the
coordinate weights, rather than the ordinary word length. -/
theorem taylorWordMonomial_homogeneous (G : HomogeneousGroup N)
    (J : List (Fin N)) (r : ℝ) (u : Fin N → ℝ) :
    taylorWordMonomial J (G.dilate r u) =
      r ^ (J.map G.weight).sum * taylorWordMonomial J u := by
  induction J with
  | nil => simp only [taylorWordMonomial_nil, List.map_nil, List.sum_nil, pow_zero, one_mul]
  | cons j J ih =>
    rw [taylorWordMonomial_cons, ih, taylorWordMonomial_cons]
    simp only [HomogeneousGroup.dilate, coordinateDilation, List.map_cons, List.sum_cons, pow_add]
    ring

end RothschildStein.P1
