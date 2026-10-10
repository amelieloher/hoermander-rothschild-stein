-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.GlobalHorizontalResolvent
public import HeatKernel.Kernel.GlobalPullbackCompatibility
public import HeatKernel.Kernel.HorizontalResolventCovariance

/-! # Horizontal resolvent covariance on full-volume L²

Translation and dilation covariance of the horizontal form graph pass
through the canonical spatial isometry to the full-volume group unitaries.
-/

@[expose] public section

noncomputable section

open MeasureTheory RothschildStein

namespace HeatKernel

/-- Full-volume left translation preserves the graph of the global horizontal resolvent. -/
theorem inverseResolventGraph_globalHorizontalForm_leftTranslation {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (y : Fin N → ℝ)
    {u g : Lp ℝ 2 (volume : Measure (Fin N → ℝ))}
    (hu : InverseResolventGraph (globalHorizontalFormResolvent G hq) u g) :
    InverseResolventGraph (globalHorizontalFormResolvent G hq)
      (leftTranslationL2 G y u) (leftTranslationL2 G y g) := by
  let e := globalSpatialL2Equiv N
  have h := inverseResolventGraph_horizontalForm_leftTranslation G hq y
    ((inverseResolventGraph_globalHorizontalForm_iff G hq u g).mp hu)
  have ht := (inverseResolventGraph_conjugate_isometry e
    (horizontalFormResolvent ⊤ (G.horizontalFields hq)) _ _).mpr h
  simpa only [globalHorizontalFormResolvent, e, globalSpatialL2Equiv_spatialLeftTranslation,
    LinearIsometryEquiv.apply_symm_apply] using ht

/-- Full-volume normalized dilation scales the global horizontal operator graph by its squared factor. -/
theorem inverseResolventGraph_globalHorizontalForm_dilation {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1) {r : ℝ} (hr : 0 < r)
    {u g : Lp ℝ 2 (volume : Measure (Fin N → ℝ))}
    (hu : InverseResolventGraph (globalHorizontalFormResolvent G hq) u g) :
    InverseResolventGraph (globalHorizontalFormResolvent G hq)
      (dilationL2Equiv G hr u) (r ^ 2 • dilationL2Equiv G hr g) := by
  let e := globalSpatialL2Equiv N
  have h := inverseResolventGraph_horizontalForm_normalizedDilation G hq hw hr
    ((inverseResolventGraph_globalHorizontalForm_iff G hq u g).mp hu)
  have ht := (inverseResolventGraph_conjugate_isometry e
    (horizontalFormResolvent ⊤ (G.horizontalFields hq)) _ _).mpr h
  simpa only [globalHorizontalFormResolvent, e, map_smul, globalSpatialL2Equiv_spatialNormalizedDilation,
    LinearIsometryEquiv.apply_symm_apply] using ht

end HeatKernel
