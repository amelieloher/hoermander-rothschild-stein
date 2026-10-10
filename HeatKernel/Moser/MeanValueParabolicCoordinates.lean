-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.GroupCutoffCovariance
public import RothschildStein.G2.DilationMeasure
public import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic

/-! # Parabolic group coordinates and their spacetime Jacobian -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory RothschildStein RothschildStein.G2
open scoped ENNReal
namespace HeatKernel

/-- Time translation followed by the quadratic scale associated with a spatial radius. -/
def parabolicTimeHomeomorph (t₀ r : ℝ) (hr : 0 < r) : ℝ ≃ₜ ℝ :=
  (Homeomorph.mulLeft₀ (r ^ 2) (pow_ne_zero _ hr.ne')).trans (Homeomorph.addLeft t₀)

/-- Parabolic coordinates combine quadratic time scaling with left translation and
homogeneous group dilation in space. -/
def parabolicGroupHomeomorph {N : ℕ} (G : HomogeneousGroup N)
    (t₀ : ℝ) (x₀ : Fin N → ℝ) (r : ℝ) (hr : 0 < r) :
    (ℝ × (Fin N → ℝ)) ≃ₜ (ℝ × (Fin N → ℝ)) :=
  (parabolicTimeHomeomorph t₀ r hr).prodCongr
    ((dilationHomeomorph G r hr).trans (leftTranslationHomeomorph G x₀))

/-- The coordinate map has the literal parabolic translation-dilation formula. -/
@[simp] theorem parabolicGroupHomeomorph_apply {N : ℕ} (G : HomogeneousGroup N)
    (t₀ : ℝ) (x₀ : Fin N → ℝ) (r : ℝ) (hr : 0 < r) (z : ℝ × (Fin N → ℝ)) :
    parabolicGroupHomeomorph G t₀ x₀ r hr z =
      (t₀ + r ^ 2 * z.1, G.mul x₀ (G.dilate r z.2)) := rfl

/-- The time coordinate pushforward has the inverse quadratic Jacobian. -/
theorem map_parabolicTimeHomeomorph_volume (t₀ r : ℝ) (hr : 0 < r) :
    Measure.map (parabolicTimeHomeomorph t₀ r hr) volume =
      ENNReal.ofReal ((r ^ 2)⁻¹) • volume := by
  change Measure.map ((t₀ + ·) ∘ (r ^ 2 * ·)) volume = _
  rw [← Measure.map_map (by fun_prop) (by fun_prop),
    Real.map_volume_mul_left (pow_ne_zero _ hr.ne'),
    Measure.map_smul _ (measurable_const_add t₀).aemeasurable,
    map_add_left_eq_self]
  rw [abs_of_nonneg (inv_nonneg.mpr (sq_nonneg r))]

/-- Left translation does not alter the homogeneous spatial dilation Jacobian. -/
theorem map_leftTranslation_dilation_volume {N : ℕ} (G : HomogeneousGroup N)
    (x₀ : Fin N → ℝ) (r : ℝ) (hr : 0 < r) :
    Measure.map (fun x => G.mul x₀ (G.dilate r x)) volume =
      ENNReal.ofReal ((r ^ G.homogeneousDimension)⁻¹) • volume := by
  change Measure.map (G.mul x₀ ∘ G.dilate r) volume = _
  rw [← Measure.map_map (measurePreserving_leftTranslation G x₀).measurable
      (contDiff_dilate G r).continuous.measurable,
    map_dilate_volume G hr,
    Measure.map_smul _ (measurePreserving_leftTranslation G x₀).measurable.aemeasurable,
    (measurePreserving_leftTranslation G x₀).map_eq]

/-- The full spacetime coordinate pushforward has inverse Jacobian r to the power Q+2. -/
theorem map_parabolicGroupHomeomorph_volume {N : ℕ} (G : HomogeneousGroup N)
    (t₀ : ℝ) (x₀ : Fin N → ℝ) (r : ℝ) (hr : 0 < r) :
    Measure.map (parabolicGroupHomeomorph G t₀ x₀ r hr) volume =
      ENNReal.ofReal ((r ^ (G.homogeneousDimension + 2))⁻¹) • volume := by
  change Measure.map
    (Prod.map (parabolicTimeHomeomorph t₀ r hr) (fun x => G.mul x₀ (G.dilate r x)))
      (volume.prod volume) = _
  have hm : Measurable (fun x => G.mul x₀ (G.dilate r x)) :=
    (contDiff_leftTranslation G x₀).continuous.measurable.comp
      (contDiff_dilate G r).continuous.measurable
  rw [← Measure.map_prod_map volume volume
    (parabolicTimeHomeomorph t₀ r hr).measurable hm,
    map_parabolicTimeHomeomorph_volume t₀ r hr,
    map_leftTranslation_dilation_volume G x₀ r hr,
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
    ← ENNReal.ofReal_mul (inv_nonneg.mpr (sq_nonneg r))]
  congr 2
  simp only [pow_add, mul_inv_rev]

end HeatKernel
