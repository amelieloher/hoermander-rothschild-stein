-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.GlobalComplexSpatialL2
public import HeatKernel.Kernel.GlobalHorizontalHeatOperators
public import HeatKernel.Kernel.TransportedRealHeatOperators
public import HeatKernel.Semigroup.HorizontalComplexResolvent

/-! # Realization of the global horizontal heat family

The canonical real-subspace embedding intertwines the concrete horizontal
resolvents. Its transported complex functional calculus is exactly the
full-volume horizontal heat family.
-/

@[expose] public section

noncomputable section

open MeasureTheory RothschildStein TopologicalSpace
open scoped NNReal

namespace HeatKernel

/-- The canonical real embedding intertwines the global and native complex horizontal resolvents. -/
theorem globalSpatialRealSubspaceEquiv_resolvent {n q : ℕ}
    (G : HomogeneousGroup n) (hq : q ≤ n)
    (f : Lp ℝ 2 (volume : Measure (Fin n → ℝ))) :
    (globalSpatialRealSubspaceEquiv n (globalHorizontalFormResolvent G hq f) :
      Lp ℂ 2 (volume.restrict ((⊤ : Opens (Fin n → ℝ)) : Set (Fin n → ℝ)))) =
    complexL2Extension (volume.restrict ((⊤ : Opens (Fin n → ℝ)) : Set (Fin n → ℝ)))
      (horizontalFormResolvent ⊤ (G.horizontalFields hq)) (globalSpatialRealSubspaceEquiv n f) := by
  change l2OfReal _ ((globalSpatialL2Equiv n).symm (globalHorizontalFormResolvent G hq f)) =
    complexL2Extension _ _ (l2OfReal _ ((globalSpatialL2Equiv n).symm f))
  have hglobal : globalHorizontalFormResolvent G hq f = globalSpatialL2Equiv n
      (horizontalFormResolvent ⊤ (G.horizontalFields hq) ((globalSpatialL2Equiv n).symm f)) := rfl
  rw [hglobal, LinearIsometryEquiv.symm_apply_apply, complexL2Extension_ofReal]

/-- The native complex resolvent realization gives exactly the concrete full-volume heat operator. -/
theorem globalHorizontalHeatOperator_eq_transport {n q : ℕ}
    (G : HomogeneousGroup n) (hq : q ≤ n) (t : ℝ≥0) :
    globalHorizontalHeatOperator G hq t =
      transportedRealHeatOperator
        (realL2Subspace (volume.restrict ((⊤ : Opens (Fin n → ℝ)) : Set (Fin n → ℝ))))
        (isClosed_realL2Subspace _)
        (complexL2Extension _ (horizontalFormResolvent ⊤ (G.horizontalFields hq)))
        (horizontalFormResolvent_complex_isSelfAdjoint ⊤ (G.horizontalFields hq))
        (mapsTo_complexL2Extension_realL2Subspace _ _)
        (spectrum_horizontalFormResolvent_complex_subset ⊤ (G.horizontalFields hq))
        (globalSpatialRealSubspaceEquiv n) t := by
  ext1 f
  rfl

end HeatKernel
