-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.BarrierRate

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H1
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- Fields realizing the comparison operator
sum Y_i² + a Y_0 for an arbitrary real drift coefficient a (BB p. 249). -/
def driftCoefficientFields (H : StandingHypotheses G q) (a : ℝ)
    (i : Fin (q + 1)) : (Fin N → ℝ) → (Fin N → ℝ) :=
  if i = 0 then a • H.fields 0 else H.fields i

/-- The comparison fields are smooth, including a=0 (BB p. 249). -/
theorem driftCoefficientFields_smooth (H : StandingHypotheses G q) (a : ℝ) (i : Fin (q + 1)) :
    ContDiff ℝ (⊤ : ℕ∞) (driftCoefficientFields G H a i) := by
  unfold driftCoefficientFields
  split_ifs
  · exact (H.fields_smooth G 0).const_smul a
  · exact H.fields_smooth G i

/-- The drift condition gives the normalized exponential identity for
every real drift coefficient, and the first drift component is zero
(BB Proposition 6.9, p. 257; Proposition 6.1, p. 249). -/
theorem driftCoefficientFields_barrier (H : StandingHypotheses G q) (a : ℝ) (x : Fin N → ℝ) :
    sumSquaresWithDrift (driftCoefficientFields G H a)
      (fun y => Real.exp (barrierRate G H * y (firstIndex G))) x =
      Real.exp (barrierRate G H * x (firstIndex G)) := by
  have h0 : fieldDerivative (H.fields 0)
      (fun y => Real.exp (barrierRate G H * y (firstIndex G))) x = 0 := by
    rw [fieldDerivative_exp_coordinate, H.drift_first_zero G]
    simp only [mul_zero, zero_mul]
  have ha0 : fieldDerivative (driftCoefficientFields G H a 0)
      (fun y => Real.exp (barrierRate G H * y (firstIndex G))) x = 0 := by
    rw [fieldDerivative_exp_coordinate]
    simp only [driftCoefficientFields, ite_true, Pi.smul_apply, smul_eq_mul,
      H.drift_first_zero G, mul_zero, zero_mul]
  have h := H.operator_barrier G x
  unfold sumSquaresWithDrift at h ⊢
  rw [ha0]
  rw [h0] at h
  simpa only [driftCoefficientFields, Fin.succ_ne_zero, ite_false] using h

end RothschildStein.H1
