-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.InversionFields

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open RothschildStein
namespace HeatKernel

/-- The derivatives in the two variables of a group convolution kernel have opposite
signs along the same left-invariant direction. -/
theorem fieldDerivative_group_kernel_swap {N : ℕ} (G : HomogeneousGroup N)
    (v x z : Fin N → ℝ) {ψ : (Fin N → ℝ) → ℝ} (hψ : ContDiff ℝ 1 ψ) :
    fieldDerivative (G2.leftField G v) (fun y => ψ (G.mul y (G.inv z))) x =
      -fieldDerivative (G2.leftField G v) (fun y => ψ (G.mul x (G.inv y))) z := by
  let A := fun y => ψ (G.mul y (G.inv z))
  let B := fun y => ψ (G.mul x (G.inv y))
  let H := A ∘ G.mul x
  have hA : ContDiff ℝ 1 A :=
    hψ.comp ((G2.contDiff_rightTranslation G (G.inv z)).of_le (by simp))
  have hB : ContDiff ℝ 1 B :=
    hψ.comp (((G2.contDiff_leftTranslation G x).of_le (by simp)).comp
      ((G2.contDiff_inv G).of_le (by simp)))
  have hH : ContDiff ℝ 1 H :=
    hA.comp ((G2.contDiff_leftTranslation G x).of_le (by simp))
  have he : B ∘ G.mul z = H ∘ G.inv := by
    funext a
    dsimp only [B, H, A, Function.comp_apply]
    rw [G2.inv_product, G2.mul_assoc]
  have hdB := fderiv_comp (𝕜 := ℝ) 0
    (hB.differentiable (by norm_num)).differentiableAt
    ((G2.contDiff_leftTranslation G z).differentiable (by simp)).differentiableAt
  have hdH := fderiv_comp (𝕜 := ℝ) 0
    (hH.differentiable (by norm_num)).differentiableAt
    ((G2.contDiff_inv G).differentiable (by simp)).differentiableAt
  have hdA := fderiv_comp (𝕜 := ℝ) 0
    (hA.differentiable (by norm_num)).differentiableAt
    ((G2.contDiff_leftTranslation G x).differentiable (by simp)).differentiableAt
  rw [G2.mul_zero, he, hdH, G2.inv_zero, (G2.inv_hasFDerivAt_zero G).fderiv] at hdB
  have hv := congrArg (fun L => L v) hdB
  change fderiv ℝ H 0 (-v) = fderiv ℝ B z (G2.leftField G v z) at hv
  have hAx : fderiv ℝ H 0 v = fderiv ℝ A x (G2.leftField G v x) := by
    dsimp only [H]
    rw [hdA, G2.mul_zero]
    rfl
  rw [map_neg, hAx] at hv
  change fderiv ℝ A x (G2.leftField G v x) = -fderiv ℝ B z (G2.leftField G v z)
  exact neg_eq_iff_eq_neg.mp hv

end HeatKernel
