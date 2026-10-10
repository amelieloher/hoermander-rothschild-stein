-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueBilinearPowerCoercivity
public import HeatKernel.Form.Ellipticity
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

/-! # Finite-matrix absorption for truncated-power energy tests

The coefficient pairing is realized as a continuous bilinear form on finite
coordinates. Ellipticity uses the sum of coordinate squares, retaining the
literal horizontal metric rather than a choice of coordinate norm.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeatKernel

/-- The continuous bilinear pairing of a finite real coefficient matrix. -/
def finiteMatrixContinuousBilinear {ι : Type*} [Fintype ι] (a : ι → ι → ℝ) :
    (ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℝ :=
  ∑ i, ∑ j, a i j •
    ((ContinuousLinearMap.proj j : (ι → ℝ) →L[ℝ] ℝ).smulRight
      (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ))

/-- The finite continuous pairing has exactly the coefficient-density orientation. -/
theorem finiteMatrixContinuousBilinear_apply {ι : Type*} [Fintype ι]
    (a : ι → ι → ℝ) (g d : ι → ℝ) :
    finiteMatrixContinuousBilinear a g d = ∑ i, ∑ j, a i j * g j * d i := by
  simp only [finiteMatrixContinuousBilinear, sum_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Finite-matrix ellipticity and absorption control the truncated half-power
horizontal energy. The cutoff errors retain both truncation regions explicitly. -/
theorem caccioppoli_matrix_half_power_flux {ι : Type*} [Fintype ι]
    (a : ι → ι → ℝ) (hsym : ∀ i j, a i j = a j i)
    (hpos : ∀ ξ, 0 ≤ matrixEnergy a ξ) {ell upper M p s : ℝ}
    (hM : 0 < M) (hp : 2 ≤ p) (hs : 0 ≤ s) (η : ℝ) (g d : ι → ℝ)
    (hlower : ell * coordinateNormSq g ≤ matrixEnergy a g)
    (hupper : matrixEnergy a d ≤ upper * coordinateNormSq d) :
    (ell / p) * linearTailPositivePowerSlope M (p / 2) s ^ 2 * η ^ 2 *
        coordinateNormSq g ≤
      linearTailPositivePowerSlope M (p - 1) s * η ^ 2 * matrixEnergy a g +
      2 * (linearTailPowerWeakSolutionTest hM (show 1 ≤ p - 1 by linarith)).toFun s *
        η * (∑ i, ∑ j, a i j * g j * d i) +
      upper * (if s < M then (2 / (p - 1)) * s ^ p else
        2 * (s ^ 2 * M ^ (p - 2))) * coordinateNormSq d := by
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
  have h := linearTail_half_power_bilinear_absorption B hbsym hbpos hM hp hs η g d
  rw [hbself, hbself, finiteMatrixContinuousBilinear_apply] at h
  have hp1 : 0 ≤ p - 1 := by linarith
  have hcut : 0 ≤ (if s < M then (2 / (p - 1)) * s ^ p else
      2 * (s ^ 2 * M ^ (p - 2))) := by split_ifs <;> positivity
  have hl := mul_le_mul_of_nonneg_left hlower
    (show 0 ≤ (1 / p) * linearTailPositivePowerSlope M (p / 2) s ^ 2 * η ^ 2 by positivity)
  have hu := mul_le_mul_of_nonneg_left hupper hcut
  simp only [div_eq_mul_inv] at *
  nlinarith

end HeatKernel
