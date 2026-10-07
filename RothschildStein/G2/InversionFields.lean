-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.OperatorInvariance

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

@[expose] public section
noncomputable section
namespace RothschildStein.G2
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Inversion sends a left-invariant tangent vector to the negative matching
right-invariant tangent vector (BB Remark 3.32, p. 112). -/
theorem inv_fderiv_leftField (v x : Fin N → ℝ) :
    fderiv ℝ G.inv x (leftField G v x) = -rightField G v (G.inv x) := by
  have he : G.inv ∘ G.mul x = (fun y => G.mul y (G.inv x)) ∘ G.inv := by
    funext y
    exact inv_product G x y
  have hd₁ := fderiv_comp 0
    ((contDiff_inv G).differentiable (by simp)).differentiableAt
    ((contDiff_leftTranslation G x).differentiable (by simp)).differentiableAt
  have hd₂ := fderiv_comp 0
    ((contDiff_rightTranslation G (G.inv x)).differentiable (by simp)).differentiableAt
    ((contDiff_inv G).differentiable (by simp)).differentiableAt
  rw [mul_zero G x, he, hd₂, inv_zero G, (inv_hasFDerivAt_zero G).fderiv] at hd₁
  have h := congrArg (fun L => L v) hd₁
  simpa [leftField, rightField] using h.symm

/-- Inversion intertwines left and right actions with a minus sign
(BB Lemma 11.21, (11.26), p. 553; no reflection assumption needed). -/
theorem rightField_action_inv (v : Fin N → ℝ) (f : (Fin N → ℝ) → ℝ)
    (hf : Differentiable ℝ f) (x : Fin N → ℝ) :
    fieldDerivative (rightField G v) f x =
      -fieldDerivative (leftField G v) (f ∘ G.inv) (G.inv x) := by
  unfold fieldDerivative
  rw [fderiv_comp (G.inv x) hf.differentiableAt
    ((contDiff_inv G).differentiable (by simp)).differentiableAt]
  change _ = -fderiv ℝ f (G.inv (G.inv x))
    (fderiv ℝ G.inv (G.inv x) (leftField G v (G.inv x)))
  rw [inv_fderiv_leftField, inv_inv G x, map_neg, neg_neg]

end RothschildStein.G2
