-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.SmoothGaugeCutoffs
public import RothschildStein.H3.HomogeneousOperators
public import RothschildStein.H3.HomogeneousBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.H3
open G2
variable {N : ℕ} {G : HomogeneousGroup N}

/-- The exterior-cutoff kernel, with the smooth gauge rather
than the generally nonsmooth control norm (BB pp. 370, 578). -/
def exteriorCutoffKernel (ν : (Fin N → ℝ) → ℝ) (φ : ℝ → ℝ)
    (F : (Fin N → ℝ) → ℝ) (ε : ℝ) (x : Fin N → ℝ) : ℝ :=
  (1 - φ (ν x / ε)) * F x

/-- Inverse dilation of a punctured homogeneous function has
exactly the expected scalar factor, independently of its value at zero. -/
theorem homogeneous_function_inverse_dilation {F : (Fin N → ℝ) → ℝ} {γ : ℝ}
    (hh : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 → F (G.dilate t x) = t ^ γ * F x)
    {ε : ℝ} (hε : 0 < ε) {x : Fin N → ℝ} (hx : x ≠ 0) :
    F x = ε ^ γ * F (G.dilate ε⁻¹ x) := by
  have hz : G.dilate ε⁻¹ x ≠ 0 := by
    intro he
    exact hx ((dilate_bijective G (inv_ne_zero hε.ne')).injective
      (he.trans (dilate_zero G ε⁻¹).symm))
  have h := hh ε hε (G.dilate ε⁻¹ x) hz
  rw [dilate_dilate G, mul_inv_cancel₀ hε.ne', dilate_one G] at h
  exact h

/-- The regularized kernel is a scalar multiple of the inverse
dilation of the unit-scale regularized kernel, including at the origin. -/
theorem exteriorCutoffKernel_scale {ν F : (Fin N → ℝ) → ℝ}
    (hν : G.IsHomogeneousGauge ν) {φ : ℝ → ℝ}
    (hone : ∀ t : ℝ, t ≤ 1 / 2 → φ t = 1) {γ : ℝ}
    (hh : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 → F (G.dilate t x) = t ^ γ * F x)
    {ε : ℝ} (hε : 0 < ε) :
    exteriorCutoffKernel ν φ F ε =
      fun x => ε ^ γ * exteriorCutoffKernel ν φ F 1 (G.dilate ε⁻¹ x) := by
  funext x
  by_cases hx : x = 0
  · subst x
    simp [exteriorCutoffKernel, dilate_zero G, (hν.2.2.1 0).mpr rfl,
      hone 0 (by norm_num)]
  · have hv : ν (G.dilate ε⁻¹ x) = ν x / ε := by
      rw [hν.2.2.2 ε⁻¹ (inv_pos.mpr hε)]
      ring
    unfold exteriorCutoffKernel
    rw [div_one, hv, homogeneous_function_inverse_dilation hh hε hx]
    ring

end RothschildStein.H3
