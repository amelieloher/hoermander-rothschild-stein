-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.MollifierDefs
public import RothschildStein.G2.ConvolutionSupport

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory Set
namespace RothschildStein.G2
variable {N : ℕ} (G : HomogeneousGroup N) {ν : HomogeneousNorm G}

/-- Positive scaling preserves nonnegativity (BB p. 121). -/
theorem groupMollifierScale_nonneg (φ : GroupMollifier G ν) {ε : ℝ}
    (hε : 0 < ε) (x : Fin N → ℝ) : 0 ≤ groupMollifierScale G φ ε x :=
  mul_nonneg (inv_nonneg.mpr (pow_nonneg hε.le _)) (φ.nonneg _)

/-- The scaled bump vanishes when the gauge is at least ε
(BB Prop 3.48, p. 121). -/
theorem groupMollifierScale_vanish (φ : GroupMollifier G ν) {ε : ℝ}
    (hε : 0 < ε) (x : Fin N → ℝ) (hx : ε ≤ ν x) :
    groupMollifierScale G φ ε x = 0 := by
  have hν : 1 ≤ ν (G.dilate ε⁻¹ x) := by
    rw [ν.gauge.2.2.2 ε⁻¹ (inv_pos.mpr hε) x]
    calc
      1 = ε⁻¹ * ε := (inv_mul_cancel₀ hε.ne').symm
      _ ≤ ε⁻¹ * ν x := mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hε.le)
  simp only [groupMollifierScale, φ.vanish _ hν, MulZeroClass.mul_zero]

/-- The scaled bump has integral one (BB (3.4), Prop 3.48,
pp. 95, 121). -/
theorem integral_groupMollifierScale (φ : GroupMollifier G ν) {ε : ℝ}
    (hε : 0 < ε) : (∫ x, groupMollifierScale G φ ε x) = 1 := by
  unfold groupMollifierScale
  rw [integral_const_mul, integral_dilate G (inv_pos.mpr hε)]
  simp only [smul_eq_mul, φ.integral_eq_one, inv_pow, mul_one]
  exact mul_inv_cancel₀ (inv_ne_zero (pow_ne_zero _ hε.ne'))

/-- Scaling preserves smoothness (BB p. 121). -/
theorem contDiff_groupMollifierScale (φ : GroupMollifier G ν) (ε : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (groupMollifierScale G φ ε) := by
  have hd : ContDiff ℝ (⊤ : ℕ∞) (G.dilate ε⁻¹) := by
    have h := (dilationLinearMap G ε⁻¹).toContinuousLinearMap.contDiff (n := (⊤ : ℕ∞))
    have he : ⇑((dilationLinearMap G ε⁻¹).toContinuousLinearMap) = G.dilate ε⁻¹ :=
      funext (dilationLinearMap_apply G ε⁻¹)
    rw [he] at h
    exact h
  exact contDiff_const.mul (φ.smooth.comp hd)

/-- Positive dilation preserves compact support (BB p. 121). -/
theorem hasCompactSupport_groupMollifierScale (φ : GroupMollifier G ν) {ε : ℝ}
    (hε : 0 < ε) : HasCompactSupport (groupMollifierScale G φ ε) := by
  let e : (Fin N → ℝ) ≃ₜ (Fin N → ℝ) :=
    { toFun := G.dilate ε⁻¹
      invFun := G.dilate ε
      left_inv := by
        intro x
        rw [dilate_dilate, mul_inv_cancel₀ hε.ne', dilate_one]
      right_inv := dilate_inv_dilate G hε.ne'
      continuous_toFun := continuous_dilate G ε⁻¹
      continuous_invFun := continuous_dilate G ε }
  exact (φ.compact.comp_homeomorph e).mul_left

/-- Positive scaling gives an integrable bump (BB p. 121). -/
theorem integrable_groupMollifierScale (φ : GroupMollifier G ν) {ε : ℝ}
    (hε : 0 < ε) : Integrable (groupMollifierScale G φ ε) :=
  (contDiff_groupMollifierScale G φ ε).continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_groupMollifierScale G φ hε)

/-- The support is contained in the ε gauge ball (BB p. 121). -/
theorem support_groupMollifierScale_subset (φ : GroupMollifier G ν) {ε : ℝ}
    (hε : 0 < ε) : Function.support (groupMollifierScale G φ ε) ⊆ {x | ν x < ε} := by
  intro x hx
  by_contra hn
  exact hx (groupMollifierScale_vanish G φ hε x (le_of_not_gt hn))

end RothschildStein.G2
