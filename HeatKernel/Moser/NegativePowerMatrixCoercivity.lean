-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.NegativePowerBilinearCoercivity
public import HeatKernel.Moser.CaccioppoliMatrixPowerFlux
import all Mathlib.Basic.Real.Basic

/-! Reciprocal-power coercivity in the horizontal coordinate-square energy. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory
namespace HeatKernel

/-- Finite-matrix negative-power absorption preserves the exact horizontal
coordinate-square diffusion and cutoff terms, uniformly in the positive exponent. -/
theorem negative_power_matrix_half_power_flux {ι : Type*} [Fintype ι]
    (a : ι → ι → ℝ) (hsym : ∀ i j, a i j = a j i)
    (hpos : ∀ ξ, 0 ≤ matrixEnergy a ξ) {ell upper p s : ℝ}
    (hell : 0 < ell) (hp : 0 < p) (hs : 0 < s) (η : ℝ) (g d : ι → ℝ)
    (hlower : ell * coordinateNormSq g ≤ matrixEnergy a g)
    (hupper : matrixEnergy a d ≤ upper * coordinateNormSq d) :
    2 * ell * (p / 2 * s ^ (-p / 2 - 1)) ^ 2 * η ^ 2 * coordinateNormSq g ≤
      p * ((p + 1) * s ^ (-p - 2) * η ^ 2 * matrixEnergy a g -
        2 * s ^ (-p - 1) * η * (∑ i, ∑ j, a i j * g j * d i)) +
      2 * upper * s ^ (-p) * coordinateNormSq d := by
  let B := finiteMatrixContinuousBilinear a
  have hbself (v : ι → ℝ) : B v v = matrixEnergy a v :=
    finiteMatrixContinuousBilinear_apply a v v
  have hbsym (v w : ι → ℝ) : B v w = B w v := by
    simp only [B, finiteMatrixContinuousBilinear_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hsym j i]
    ring
  have hbpos (v : ι → ℝ) : 0 ≤ B v v := by rw [hbself]; exact hpos v
  have habs := mul_le_mul_of_nonneg_left
    (negative_power_bilinear_absorption B hbsym hbpos hp hs η g d) hp.le
  rw [hbself, hbself, finiteMatrixContinuousBilinear_apply] at habs
  have hnorm : 0 ≤ coordinateNormSq g := by
    unfold coordinateNormSq
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hgrad := mul_le_mul_of_nonneg_right
    (negative_half_power_gradient_le_half_principal hell hp hs η 1) hnorm
  have hprincipal := mul_le_mul_of_nonneg_left hlower
    (show 0 ≤ p * (p + 1) / 2 * s ^ (-p - 2) * η ^ 2 by positivity)
  have hcoef : p * (2 / (p + 1)) ≤ 2 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by linarith : 0 < p + 1)).mpr
    linarith
  have hcut := mul_le_mul_of_nonneg_right hcoef
    (mul_nonneg (Real.rpow_nonneg hs.le (-p)) (hpos d))
  have hbound := mul_le_mul_of_nonneg_left hupper
    (show 0 ≤ 2 * s ^ (-p) by positivity)
  nlinarith

end HeatKernel
