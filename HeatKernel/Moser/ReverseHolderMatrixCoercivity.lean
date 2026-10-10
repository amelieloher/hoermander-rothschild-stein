-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.CaccioppoliBilinearAbsorption
public import HeatKernel.Moser.ReverseHolderCoefficients
public import HeatKernel.Moser.CaccioppoliMatrixPowerFlux
import all Mathlib.Basic.Real.Basic

/-! Uniform concave-power absorption in the horizontal coordinate-square energy. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory
namespace HeatKernel

/-- Small positive exponents retain a uniform half-power gradient bound after
absorbing the mixed matrix flux. Horizontal energy is the sum of coordinate squares. -/
theorem reverse_holder_matrix_half_power_absorption {ι : Type*} [Fintype ι]
    (a : ι → ι → ℝ) (hsym : ∀ i j, a i j = a j i)
    (hpos : ∀ ξ, 0 ≤ matrixEnergy a ξ) {ell upper p : ℝ}
    (hell : 0 ≤ ell) (hp : 0 < p) (hp2 : p ≤ 1 / 2) (v w : ι → ℝ)
    (hlower : ell * coordinateNormSq v ≤ matrixEnergy a v)
    (hupper : matrixEnergy a w ≤ upper * coordinateNormSq w) :
    2 * ell * (p / 2) ^ 2 * coordinateNormSq v ≤
      p * ((1 - p) * matrixEnergy a v - 2 * (∑ i, ∑ j, a i j * v j * w i)) +
        2 * upper * coordinateNormSq w := by
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
  have hraw := caccioppoli_weighted_bilinear_absorption B hbsym hbpos
    (by linarith : 0 < 1 - p) (by norm_num : (0 : ℝ) ≤ 1) (-1) 1 v w
  have hpair : B v w = ∑ i, ∑ j, a i j * v j * w i :=
    finiteMatrixContinuousBilinear_apply a v w
  have hbase : (1 - p) / 2 * matrixEnergy a v - (2 / (1 - p)) * matrixEnergy a w ≤
      (1 - p) * matrixEnergy a v - 2 * (∑ i, ∑ j, a i j * v j * w i) := by
    simpa only [hbself, hpair, one_pow, neg_one_sq,
      mul_one, mul_neg, mul_add, mul_sub, one_mul, sub_eq_add_neg, neg_mul] using hraw
  have habs := mul_le_mul_of_nonneg_left hbase hp.le
  have hnorm : 0 ≤ coordinateNormSq v := by
    unfold coordinateNormSq
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcoef : 2 * ell * (p / 2) ^ 2 ≤ p * ((1 - p) / 2) * ell := by
    have hprod := mul_nonneg hp.le (show 0 ≤ 1 - 2 * p by linarith)
    have hscaled := mul_nonneg hell hprod
    nlinarith
  have hgrad := mul_le_mul_of_nonneg_right hcoef hnorm
  have hprincipal := mul_le_mul_of_nonneg_left hlower
    (show 0 ≤ p * ((1 - p) / 2) from
      mul_nonneg hp.le (div_nonneg (by linarith) (by norm_num)))
  have hcutcoef : p * (2 / (1 - p)) ≤ 2 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by linarith : 0 < 1 - p)).mpr
    linarith
  have hcut := mul_le_mul_of_nonneg_right hcutcoef (hpos w)
  have hbound := mul_le_mul_of_nonneg_left hupper (by norm_num : (0 : ℝ) ≤ 2)
  nlinarith

end HeatKernel
