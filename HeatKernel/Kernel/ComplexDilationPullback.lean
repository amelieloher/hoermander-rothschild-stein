-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.ComplexScaledMeasurePullbacks
public import HeatKernel.Kernel.DilationUnitary

/-! # Normalized complex L² dilation

The Haar Jacobian fixes the square-root normalization of complex L² pullback.
The resulting complex linear map preserves the Hermitian inner product.
-/

@[expose] public section

noncomputable section

open MeasureTheory RothschildStein

namespace HeatKernel

/-- The square-root Haar normalization of complex L² dilation pullback. -/
def complexNormalizedDilationL2 {n : ℕ} (G : HomogeneousGroup n) {r : ℝ} (hr : 0 < r) :
    Lp ℂ 2 (volume : Measure (Fin n → ℝ)) →L[ℂ] Lp ℂ 2 (volume : Measure (Fin n → ℝ)) :=
  (Real.sqrt (r ^ G.homogeneousDimension) : ℂ) •
    complexScaledMeasurePullback (G2.continuous_dilate G r).measurable
      (G2.map_dilate_volume G hr) ENNReal.ofReal_ne_top

/-- Normalized complex dilation has the literal scalar pullback representative. -/
theorem ae_complexNormalizedDilationL2 {n : ℕ} (G : HomogeneousGroup n) {r : ℝ} (hr : 0 < r)
    (f : Lp ℂ 2 (volume : Measure (Fin n → ℝ))) :
    complexNormalizedDilationL2 G hr f =ᵐ[volume]
      fun x => (Real.sqrt (r ^ G.homogeneousDimension) : ℂ) * f (G.dilate r x) := by
  have hscalar := Lp.coeFn_smul (Real.sqrt (r ^ G.homogeneousDimension) : ℂ)
    (complexScaledMeasurePullback (G2.continuous_dilate G r).measurable
      (G2.map_dilate_volume G hr) ENNReal.ofReal_ne_top f)
  have hpull := complexScaledMeasurePullback_ae (G2.continuous_dilate G r).measurable
    (G2.map_dilate_volume G hr) ENNReal.ofReal_ne_top f
  filter_upwards [hscalar, hpull] with x hs hp
  change ((Real.sqrt (r ^ G.homogeneousDimension) : ℂ) •
    complexScaledMeasurePullback (G2.continuous_dilate G r).measurable
      (G2.map_dilate_volume G hr) ENNReal.ofReal_ne_top f) x = _
  rw [hs]
  change (Real.sqrt (r ^ G.homogeneousDimension) : ℂ) *
    complexScaledMeasurePullback (G2.continuous_dilate G r).measurable
      (G2.map_dilate_volume G hr) ENNReal.ofReal_ne_top f x = _
  rw [hp]
  rfl

/-- Normalized complex dilation preserves the Hermitian L² inner product. -/
theorem inner_complexNormalizedDilationL2 {n : ℕ} (G : HomogeneousGroup n) {r : ℝ} (hr : 0 < r)
    (f g : Lp ℂ 2 (volume : Measure (Fin n → ℝ))) :
    inner ℂ (complexNormalizedDilationL2 G hr f) (complexNormalizedDilationL2 G hr g) =
      inner ℂ f g := by
  change inner ℂ ((Real.sqrt (r ^ G.homogeneousDimension) : ℂ) •
    complexScaledMeasurePullback (G2.continuous_dilate G r).measurable
      (G2.map_dilate_volume G hr) ENNReal.ofReal_ne_top f)
    ((Real.sqrt (r ^ G.homogeneousDimension) : ℂ) •
    complexScaledMeasurePullback (G2.continuous_dilate G r).measurable
      (G2.map_dilate_volume G hr) ENNReal.ofReal_ne_top g) = _
  rw [inner_smul_left, inner_smul_right,
    inner_complexScaledMeasurePullback (G2.measurableEmbedding_dilate G hr.ne')
      (G2.map_dilate_volume G hr) ENNReal.ofReal_ne_top f g]
  simp only [Complex.conj_ofReal, Algebra.smul_def, RCLike.algebraMap_eq_ofReal, RCLike.ofReal_eq_complex_ofReal,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (pow_pos hr _).le)]
  have hscalar : (Real.sqrt (r ^ G.homogeneousDimension) : ℂ) *
      (Real.sqrt (r ^ G.homogeneousDimension) : ℂ) *
      ((r ^ G.homogeneousDimension)⁻¹ : ℝ) = 1 := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← pow_two,
      Real.sq_sqrt (pow_pos hr _).le, mul_inv_cancel₀ (pow_ne_zero _ hr.ne'), Complex.ofReal_one]
  calc
    _ = ((Real.sqrt (r ^ G.homogeneousDimension) : ℂ) *
      (Real.sqrt (r ^ G.homogeneousDimension) : ℂ) * ((r ^ G.homogeneousDimension)⁻¹ : ℝ)) *
        inner ℂ f g := by ring
    _ = _ := by rw [hscalar, one_mul]

end HeatKernel
