-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.NormalizedDilationEquivalences

/-! # Spatial pullbacks compatible with the global horizontal form

Left translation and normalized positive dilation act on the spatial
L² space of the global form. Their spatial inner products are preserved.
-/

@[expose] public section

noncomputable section

open MeasureTheory RothschildStein

namespace HeatKernel

/-- Left translation preserves the measure used by the global spatial form. -/
theorem map_leftTranslation_restrict_univ_volume {N : ℕ} (G : HomogeneousGroup N)
    (y : Fin N → ℝ) :
    Measure.map (G2.leftTranslationHomeomorph G y)
      (volume.restrict ((⊤ : TopologicalSpace.Opens (Fin N → ℝ)) : Set (Fin N → ℝ))) =
      (1 : ENNReal) • volume.restrict
        ((⊤ : TopologicalSpace.Opens (Fin N → ℝ)) : Set (Fin N → ℝ)) := by
  change Measure.map (G.mul y) (volume.restrict Set.univ) =
    (1 : ENNReal) • volume.restrict Set.univ
  simpa only [Measure.restrict_univ, one_smul] using
    (G2.measurePreserving_leftTranslation G y).map_eq

/-- Positive dilation scales the measure used by the global spatial form. -/
theorem map_dilate_restrict_univ_volume {N : ℕ} (G : HomogeneousGroup N)
    {r : ℝ} (hr : 0 < r) :
    Measure.map (G2.dilationHomeomorph G r hr)
      (volume.restrict ((⊤ : TopologicalSpace.Opens (Fin N → ℝ)) : Set (Fin N → ℝ))) =
      ENNReal.ofReal ((r ^ G.homogeneousDimension)⁻¹) • volume.restrict
        ((⊤ : TopologicalSpace.Opens (Fin N → ℝ)) : Set (Fin N → ℝ)) := by
  change Measure.map (G.dilate r) (volume.restrict Set.univ) =
    ENNReal.ofReal ((r ^ G.homogeneousDimension)⁻¹) • volume.restrict Set.univ
  simpa only [Measure.restrict_univ] using G2.map_dilate_volume G hr

/-- Left-translation pullback on the spatial L² space of the global form. -/
def spatialLeftTranslation {N : ℕ} (G : HomogeneousGroup N) (y : Fin N → ℝ) :
    SpatialL2 (N := N) ⊤ →L[ℝ] SpatialL2 (N := N) ⊤ :=
  scaledMeasurePullback (G2.leftTranslationHomeomorph G y).continuous.measurable
    (J := 1) (map_leftTranslation_restrict_univ_volume G y) (by simp)

/-- Normalized dilation on the spatial L² space of the global form. -/
def spatialNormalizedDilation {N : ℕ} (G : HomogeneousGroup N) {r : ℝ} (hr : 0 < r) :
    SpatialL2 (N := N) ⊤ →L[ℝ] SpatialL2 (N := N) ⊤ :=
  Real.sqrt (r ^ G.homogeneousDimension) •
    scaledMeasurePullback (G2.dilationHomeomorph G r hr).continuous.measurable
      (J := ENNReal.ofReal ((r ^ G.homogeneousDimension)⁻¹))
      (map_dilate_restrict_univ_volume G hr) ENNReal.ofReal_ne_top

/-- Spatial left translation preserves the full L² inner product. -/
theorem inner_spatialLeftTranslation {N : ℕ} (G : HomogeneousGroup N) (y : Fin N → ℝ)
    (f g : SpatialL2 (N := N) ⊤) :
    inner ℝ (spatialLeftTranslation G y f) (spatialLeftTranslation G y g) = inner ℝ f g := by
  have h := inner_scaledMeasurePullback (G2.leftTranslationHomeomorph G y).measurableEmbedding
    (μ := volume.restrict ((⊤ : TopologicalSpace.Opens (Fin N → ℝ)) : Set (Fin N → ℝ)))
    (J := 1) (map_leftTranslation_restrict_univ_volume G y) (by simp) f g
  simpa only [spatialLeftTranslation, ENNReal.toReal_one, one_mul] using h

/-- Spatial normalized dilation preserves the full L² inner product. -/
theorem inner_spatialNormalizedDilation {N : ℕ} (G : HomogeneousGroup N) {r : ℝ} (hr : 0 < r)
    (f g : SpatialL2 (N := N) ⊤) :
    inner ℝ (spatialNormalizedDilation G hr f) (spatialNormalizedDilation G hr g) = inner ℝ f g := by
  have h := inner_scaledMeasurePullback (G2.dilationHomeomorph G r hr).measurableEmbedding
    (μ := volume.restrict ((⊤ : TopologicalSpace.Opens (Fin N → ℝ)) : Set (Fin N → ℝ)))
    (J := ENNReal.ofReal ((r ^ G.homogeneousDimension)⁻¹))
    (map_dilate_restrict_univ_volume G hr) ENNReal.ofReal_ne_top f g
  have hscalar : Real.sqrt (r ^ G.homogeneousDimension) ^ 2 *
      (ENNReal.ofReal ((r ^ G.homogeneousDimension)⁻¹)).toReal = 1 := by
    rw [Real.sq_sqrt (pow_nonneg hr.le _),
      ENNReal.toReal_ofReal (inv_nonneg.mpr (pow_nonneg hr.le _)),
      mul_inv_cancel₀ (pow_ne_zero _ hr.ne')]
  simp only [spatialNormalizedDilation, smul_apply,
    real_inner_smul_left, real_inner_smul_right, h]
  rw [← mul_assoc, ← mul_assoc, ← pow_two, hscalar, one_mul]

/-- Spatial translation represents composition by left multiplication. -/
theorem spatialLeftTranslation_ae {N : ℕ} (G : HomogeneousGroup N) (y : Fin N → ℝ)
    (f : SpatialL2 (N := N) ⊤) :
    spatialLeftTranslation G y f =ᵐ[volume] f ∘ G.mul y := by
  have h := scaledMeasurePullback_ae (G2.leftTranslationHomeomorph G y).continuous.measurable
    (μ := volume.restrict ((⊤ : TopologicalSpace.Opens (Fin N → ℝ)) : Set (Fin N → ℝ)))
    (J := 1) (map_leftTranslation_restrict_univ_volume G y) (by simp) f
  change spatialLeftTranslation G y f =ᵐ[volume.restrict Set.univ] f ∘ G.mul y at h
  simpa only [Measure.restrict_univ] using h

end HeatKernel
