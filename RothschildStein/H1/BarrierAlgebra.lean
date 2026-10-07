-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.OperatorAlgebra

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.H1
variable {N q : ℕ}

/-- The exponential barrier is given by BB Prop 6.1, p. 249. -/
def exponentialBarrier (j : Fin N) (γ d : ℝ) (x : Fin N → ℝ) : ℝ :=
  Real.exp (2 * γ * d) - Real.exp (γ * (x j + d))

/-- The explicit barrier is C2 (BB p. 249). -/
theorem contDiff_exponentialBarrier (j : Fin N) (γ d : ℝ) :
    ContDiff ℝ 2 (exponentialBarrier j γ d) :=
  contDiff_const.sub (Real.contDiff_exp.comp
    (contDiff_const.mul ((contDiff_apply ℝ ℝ j).add contDiff_const)))

/-- Constants are annihilated by the operator (BB p. 249). -/
theorem sumSquares_const
    (X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)) (c : ℝ) (x : Fin N → ℝ) :
    sumSquaresWithDrift X (fun _ => c) x = 0 := by
  have H (V : (Fin N → ℝ) → (Fin N → ℝ)) (c : ℝ) :
      fieldDerivative V (fun _ => c) = fun _ => 0 := by
    funext z
    simp only [fieldDerivative, fderiv_const_apply, zero_apply]
  simp only [sumSquaresWithDrift, H, Finset.sum_const_zero, zero_add]

/-- The barrier satisfies Pg = -exp(γ(x_j+d)) by the exact identity, for either choice of drift sign (BB p. 249). -/
theorem sumSquares_exponentialBarrier_of_barrier
    {X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)} (j : Fin N) (γ d : ℝ)
    (hbar : ∀ z, sumSquaresWithDrift X (fun z => Real.exp (γ * z j)) z = Real.exp (γ * z j))
    (x : Fin N → ℝ) (hX : ∀ i : Fin q, DifferentiableAt ℝ (X i.succ) x) :
    sumSquaresWithDrift X (exponentialBarrier j γ d) x = -Real.exp (γ * (x j + d)) := by
  let b : (Fin N → ℝ) → ℝ := fun z => Real.exp (γ * z j)
  have hb : ContDiff ℝ 2 b := Real.contDiff_exp.comp (contDiff_const.mul (contDiff_apply ℝ ℝ j))
  have he : exponentialBarrier j γ d =
      (fun _ : Fin N → ℝ => Real.exp (2 * γ * d)) + (fun z => -Real.exp (γ * d) * b z) := by
    funext z
    simp only [exponentialBarrier, Pi.add_apply, b, mul_add, Real.exp_add]
    ring
  rw [he, sumSquares_add_at contDiffAt_const (contDiff_const.mul hb).contDiffAt hX,
    sumSquares_const, zero_add, congrFun (sumSquares_const_mul X (-Real.exp (γ * d)) b) x]
  change -Real.exp (γ * d) * sumSquaresWithDrift X (fun z => Real.exp (γ * z j)) x = _
  rw [hbar]
  simp only [mul_add, Real.exp_add]
  ring

/-- Both bounds on the barrier are exact throughout the closed
coordinate slab (BB Prop 6.1, p. 249). -/
theorem exponentialBarrier_bounds (j : Fin N) {γ d : ℝ} (hγ : 0 ≤ γ)
    (x : Fin N → ℝ) (hx : -d ≤ x j ∧ x j ≤ d) :
    0 ≤ exponentialBarrier j γ d x ∧
      exponentialBarrier j γ d x ≤ Real.exp (2 * γ * d) - 1 := by
  have hlo : 0 ≤ γ * (x j + d) := mul_nonneg hγ (by linarith [hx.1])
  have hhi : γ * (x j + d) ≤ 2 * γ * d := by nlinarith [hx.2]
  constructor
  · exact sub_nonneg.mpr (Real.exp_le_exp.mpr hhi)
  · have H : 1 ≤ Real.exp (γ * (x j + d)) := by
      simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hlo
    unfold exponentialBarrier
    linarith

end RothschildStein.H1
