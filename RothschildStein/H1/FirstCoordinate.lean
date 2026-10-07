-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.Standing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

@[expose] public section
noncomputable section
namespace RothschildStein.H1
open scoped BigOperators
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- The first coefficient of every invariant field is constant
(BB Theorem 3.29 / Proposition 6.9, pp. 110, 256–257). -/
theorem invariant_first_coordinate
    {V : (Fin N → ℝ) → (Fin N → ℝ)} (hV : G2.IsLeftInvariantField G V)
    (x : Fin N → ℝ) : V x (firstIndex G) = V 0 (firstIndex G) := by
  rw [hV.eq_leftField G, G2.leftField_polynomial]
  have hc : ∀ i, G2.leftCoefficient G i (firstIndex G) =
      if i = firstIndex G then 1 else 0 := by
    intro i
    exact G2.leftCoefficient_of_le G i (firstIndex G) (by
      change 0 ≤ i.val
      exact Nat.zero_le _)
  simp [G2.leftFieldPolynomial, hc, G2.leftField_zero]

/-- The horizontal first coefficients are constant (BB p. 257). -/
theorem StandingHypotheses.horizontal_first_constant (H : StandingHypotheses G q)
    (i : Fin q) (x : Fin N → ℝ) :
    H.fields i.succ x (firstIndex G) = H.fields i.succ 0 (firstIndex G) :=
  invariant_first_coordinate G (H.invariant i.succ) x

/-- The drift has no first-coordinate component (BB Proposition 6.9, p. 257). -/
theorem StandingHypotheses.drift_first_zero (H : StandingHypotheses G q)
    (x : Fin N → ℝ) : H.fields 0 x (firstIndex G) = 0 := by
  rw [invariant_first_coordinate G (H.invariant 0)]
  have hh : G2.IsHomogeneousField G (G2.leftField G (H.fields 0 0)) 2 := by
    rw [← (H.invariant 0).eq_leftField G]
    simpa using H.homogeneous 0
  apply (G2.leftField_homogeneous_iff G _ _).mp hh
  rw [H.first_weight]
  norm_num

/-- The positive coefficient sought in Proposition 6.9. -/
def horizontalFirstSquareSum (H : StandingHypotheses G q) : ℝ :=
  ∑ i : Fin q, (H.fields i.succ 0 (firstIndex G)) ^ 2

end RothschildStein.H1
