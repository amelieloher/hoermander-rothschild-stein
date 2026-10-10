-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.LogarithmicCutoffEnergyBound
public import HeatKernel.Moser.LogarithmicTentGradient
public import HeatKernel.Sobolev.TentVolume
import Mathlib.Tactic
import all Mathlib.Basic.Real.Basic

/-! # Exact distance-tent normalization of the logarithmic cutoff error -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory RothschildStein
namespace HeatKernel

/-- The exact squared-tent mass cancels the supporting ball volume in the
normalized cutoff error. The resulting constant depends only on the coefficient
upper bound and homogeneous dimension. -/
theorem normalized_logarithmic_tent_cutoff_energy_le {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (x : Fin N → ℝ) {r C upper : ℝ} (hr : 0 < r)
    {a : Fin q → Fin q → (Fin N → ℝ) → ℝ} {d : Fin q → (Fin N → ℝ) → ℝ}
    (ha : ∀ i j, AEStronglyMeasurable (a i j) volume)
    (hb : ∀ i j, ∀ᵐ y ∂volume, ‖a i j y‖ ≤ C)
    (hd : ∀ i, MemLp (d i) 2 volume) (hupper : 0 ≤ upper)
    (hquad : ∀ᵐ y ∂volume, ∀ ξ, matrixEnergy (fun i j => a i j y) ξ ≤ upper * coordinateNormSq ξ)
    (hgrad : ∀ᵐ y ∂volume, y ∈ horizontalBall (G.horizontalFields hq) x r →
      coordinateNormSq (fun i => d i y) ≤ (r ^ 2)⁻¹)
    (hsupport : ∀ᵐ y ∂volume, y ∉ horizontalBall (G.horizontalFields hq) x r →
      ∀ i, d i y = 0) :
    2 * (∫ y, max (1 - (horizontalL2Distance (G.horizontalFields hq) x y).toReal / r) 0 ^ 2)⁻¹ *
      (∫ y, matrixEnergy (fun i j => a i j y) (fun i => d i y)) ≤
      upper * (((G.homogeneousDimension : ℝ) + 1) *
        ((G.homogeneousDimension : ℝ) + 2)) / r ^ 2 := by
  have hmass := Sobolev.integral_horizontal_tent_sq_pos G hq hqpos hspan hw x hr
  have he := integral_logarithmic_cutoff_energy_le_of_support
    (isOpen_horizontalBall G hq hqpos hspan x r).measurableSet
    (volume_horizontalBall_lt_top G hq hqpos hspan hw x hr.le).ne
    ha hb hd hupper hquad hgrad hsupport
  have hv : volume.real (horizontalBall (G.horizontalFields hq) x r) ≠ 0 :=
    (ENNReal.toReal_pos (volume_horizontalBall_pos G hq hqpos hspan x hr).ne'
      (volume_horizontalBall_lt_top G hq hqpos hspan hw x hr.le).ne).ne'
  have hdim : (((G.homogeneousDimension : ℝ) + 1) *
      ((G.homogeneousDimension : ℝ) + 2)) ≠ 0 := ne_of_gt (by positivity)
  have hn := mul_le_mul_of_nonneg_left he
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (inv_nonneg.mpr hmass.le))
  refine hn.trans_eq ?_
  rw [Sobolev.integral_horizontal_tent_sq G hq hqpos hspan hw x hr]
  field_simp

end HeatKernel
