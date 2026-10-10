-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.HorizontalCoreGenerator
public import HeatKernel.Semigroup.HorizontalOperatorGraph
public import RothschildStein.Definitions.sumSquares

/-! # Compact horizontal tests in the resolvent graph

The smooth compact core identity for the horizontal form identifies the
associated inverse-resolvent graph on prescribed scalar L² representatives.
-/

@[expose] public section

noncomputable section

open MeasureTheory TopologicalSpace RothschildStein

namespace HeatKernel

/-- Smooth compact scalar tests and their negative sum of squares belong to the horizontal resolvent graph. -/
theorem inverseResolventGraph_horizontalForm_of_smooth_compact {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (f : (Fin N → ℝ) → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (w g : SpatialL2 (N := N) ⊤) (hw : w =ᵐ[volume] f)
    (hg : g =ᵐ[volume] fun x => -sumSquares (G.horizontalFields hq) f x) :
    InverseResolventGraph (horizontalFormResolvent ⊤ (G.horizontalFields hq)) w g := by
  obtain ⟨u, k, hu, hk, hform⟩ := exists_horizontal_core_operatorValue G hq hf hc
  have huw : energyInclusion ⊤ (G.horizontalFields hq) u = w := by
    apply Lp.ext
    have h : energyInclusion ⊤ (G.horizontalFields hq) u =ᵐ[volume] w := hu.trans hw.symm
    simpa only [Opens.coe_top, Measure.restrict_univ] using h
  have hkg : k = g := by
    apply Lp.ext
    have h : k =ᵐ[volume] g := hk.trans hg.symm
    simpa only [Opens.coe_top, Measure.restrict_univ] using h
  apply (horizontalFormGraph_iff_inverseResolventGraph ⊤ (G.horizontalFields hq)
    (fun i => (G.horizontalFields_contDiff hq i).contDiffOn) w g).mp
  exact ⟨u, huw, by simpa only [IsWeakFormOperatorValue, hkg] using hform⟩

end HeatKernel
