-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueScaledMeasures
public import HeatKernel.Geometry.WeakGradientLinearity
public import RothschildStein.G2.InvariantDivergence
import Mathlib.Tactic

/-! # Spatial test transport for horizontal weak derivatives -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory RothschildStein RothschildStein.G2
namespace HeatKernel

/-- The spatial translation-dilation underlying parabolic coordinates. -/
def spatialGroupHomeomorph {N : ℕ} (G : HomogeneousGroup N)
    (x₀ : Fin N → ℝ) (r : ℝ) (hr : 0 < r) : (Fin N → ℝ) ≃ₜ (Fin N → ℝ) :=
  (dilationHomeomorph G r hr).trans (leftTranslationHomeomorph G x₀)

/-- Both directions of the spatial coordinate map are smooth. -/
theorem contDiff_spatialGroupHomeomorph_symm {N : ℕ} (G : HomogeneousGroup N)
    (x₀ : Fin N → ℝ) (r : ℝ) (hr : 0 < r) :
    ContDiff ℝ (⊤ : ℕ∞) (spatialGroupHomeomorph G x₀ r hr).symm :=
  (contDiff_dilate G r⁻¹).comp (contDiff_leftTranslation G (G.inv x₀))

/-- The transpose of a single horizontal field has the inverse spatial scale on
transported tests, evaluated at the coordinate image. -/
theorem wordTranspose_spatial_transport_at_image {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q ≤ N) (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (x₀ : Fin N → ℝ) (r : ℝ) (hr : 0 < r)
    {φ : (Fin N → ℝ) → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (i : Fin q) (x : Fin N → ℝ) :
    wordTranspose (G.horizontalFields hq) [i]
      (φ ∘ (spatialGroupHomeomorph G x₀ r hr).symm)
        (spatialGroupHomeomorph G x₀ r hr x) =
      r⁻¹ * wordTranspose (G.horizontalFields hq) [i] φ x := by
  let B := spatialGroupHomeomorph G x₀ r hr
  have hψ := hφ.comp (contDiff_spatialGroupHomeomorph_symm G x₀ r hr)
  have hx : G.dilate r⁻¹ (G.mul (G.inv x₀) (B x)) = x := B.symm_apply_apply x
  change fieldTranspose (G.horizontalFields hq i) (φ ∘ B.symm) (B x) =
    r⁻¹ * fieldTranspose (G.horizontalFields hq i) φ x
  rw [horizontalField_transpose G hq i hψ,
    horizontalField_transpose G hq i hφ]
  change -fieldDerivative (G.horizontalFields hq i)
    (translatedDilatedFunction G x₀ r φ) (B x) = _
  rw [fieldDerivative_translatedDilatedFunction G hq hw x₀ hr hφ, hx]
  ring

end HeatKernel
