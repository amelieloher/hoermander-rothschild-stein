-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.GlobalSpatialL2
public import HeatKernel.Kernel.SpatialDilationRepresentatives
public import HeatKernel.Kernel.TranslationKernel
public import HeatKernel.Kernel.DilationUnitary

/-! # Compatibility of global spatial and full-volume group actions

The canonical L² identification intertwines spatial form pullbacks with
the translation and normalized dilation unitaries on full-volume L².
-/

@[expose] public section

noncomputable section

open MeasureTheory RothschildStein

namespace HeatKernel

/-- The global spatial isometry intertwines the two left-translation pullbacks. -/
theorem globalSpatialL2Equiv_spatialLeftTranslation {N : ℕ}
    (G : HomogeneousGroup N) (y : Fin N → ℝ) (f : SpatialL2 (N := N) ⊤) :
    globalSpatialL2Equiv N (spatialLeftTranslation G y f) =
      leftTranslationL2 G y (globalSpatialL2Equiv N f) := by
  apply Lp.ext
  filter_upwards [ae_globalSpatialL2Equiv (spatialLeftTranslation G y f),
    spatialLeftTranslation_ae G y f,
    (G2.measurePreserving_leftTranslation G y).quasiMeasurePreserving.ae_eq_comp
      (ae_globalSpatialL2Equiv f), ae_leftTranslationL2_apply G y (globalSpatialL2Equiv N f)]
    with x he ha hcomp hb
  simp only [Function.comp_apply] at ha hcomp
  rw [he, ha, hb, hcomp]

/-- The global spatial isometry intertwines the two normalized dilation pullbacks. -/
theorem globalSpatialL2Equiv_spatialNormalizedDilation {N : ℕ}
    (G : HomogeneousGroup N) {r : ℝ} (hr : 0 < r) (f : SpatialL2 (N := N) ⊤) :
    globalSpatialL2Equiv N (spatialNormalizedDilation G hr f) =
      dilationL2Equiv G hr (globalSpatialL2Equiv N f) := by
  apply Lp.ext
  filter_upwards [ae_globalSpatialL2Equiv (spatialNormalizedDilation G hr f),
    spatialNormalizedDilation_ae G hr f,
    (quasiMeasurePreserving_group_dilate G hr).ae_eq_comp (ae_globalSpatialL2Equiv f),
    ae_dilationL2Equiv_apply G hr (globalSpatialL2Equiv N f)] with x he ha hcomp hb
  simp only [Function.comp_apply] at hcomp
  rw [he, ha, hb, hcomp]

end HeatKernel
