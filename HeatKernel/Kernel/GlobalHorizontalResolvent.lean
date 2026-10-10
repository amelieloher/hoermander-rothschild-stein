-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.GlobalSpatialL2
public import HeatKernel.Kernel.ConjugateResolventGraph
public import HeatKernel.Kernel.CompactHorizontalResolventGraph

/-! # The horizontal form resolvent on full-volume L²

The canonical global spatial isometry transports the form resolvent and
its compact smooth core to the L² space used for scalar kernel integrals.
-/

@[expose] public section

noncomputable section

open MeasureTheory RothschildStein

namespace HeatKernel

/-- The global horizontal form resolvent, expressed on full-volume real L². -/
def globalHorizontalFormResolvent {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N) :
    Lp ℝ 2 (volume : Measure (Fin N → ℝ)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (Fin N → ℝ)) :=
  (globalSpatialL2Equiv N).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((horizontalFormResolvent ⊤ (G.horizontalFields hq)).comp
      (globalSpatialL2Equiv N).symm.toContinuousLinearEquiv.toContinuousLinearMap)

/-- Transport to full-volume L² preserves self-adjointness of the horizontal resolvent. -/
theorem globalHorizontalFormResolvent_isSelfAdjoint {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) :
    IsSelfAdjoint (globalHorizontalFormResolvent G hq) := by
  change IsSelfAdjoint ((globalSpatialL2Equiv N).conjStarAlgEquiv
    (horizontalFormResolvent ⊤ (G.horizontalFields hq)))
  exact (horizontalFormResolvent_isSelfAdjoint ⊤ (G.horizontalFields hq)).map
    ((globalSpatialL2Equiv N).conjStarAlgEquiv)

/-- Graph membership on full-volume L² is equivalent to native spatial form graph membership. -/
theorem inverseResolventGraph_globalHorizontalForm_iff {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N)
    (w g : Lp ℝ 2 (volume : Measure (Fin N → ℝ))) :
    InverseResolventGraph (globalHorizontalFormResolvent G hq) w g ↔
      InverseResolventGraph (horizontalFormResolvent ⊤ (G.horizontalFields hq))
        ((globalSpatialL2Equiv N).symm w) ((globalSpatialL2Equiv N).symm g) := by
  simpa only [globalHorizontalFormResolvent, LinearIsometryEquiv.apply_symm_apply] using
    inverseResolventGraph_conjugate_isometry (globalSpatialL2Equiv N)
      (horizontalFormResolvent ⊤ (G.horizontalFields hq))
      ((globalSpatialL2Equiv N).symm w) ((globalSpatialL2Equiv N).symm g)

/-- Smooth compact scalar tests have negative horizontal sum of squares in the full-volume graph. -/
theorem inverseResolventGraph_globalHorizontalForm_of_smooth_compact {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (f : (Fin N → ℝ) → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (w g : Lp ℝ 2 (volume : Measure (Fin N → ℝ))) (hw : w =ᵐ[volume] f)
    (hg : g =ᵐ[volume] fun x => -sumSquares (G.horizontalFields hq) f x) :
    InverseResolventGraph (globalHorizontalFormResolvent G hq) w g := by
  apply (inverseResolventGraph_globalHorizontalForm_iff G hq w g).mpr
  exact inverseResolventGraph_horizontalForm_of_smooth_compact G hq f hf hc _ _
    ((ae_globalSpatialL2Equiv_symm w).trans hw)
    ((ae_globalSpatialL2Equiv_symm g).trans hg)

end HeatKernel
