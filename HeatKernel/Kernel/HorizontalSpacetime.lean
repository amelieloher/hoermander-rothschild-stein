-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.SpacetimeRank
public import RothschildStein.Definitions.HomogeneousGroup.horizontalFields_contDiff

/-! # Spacetime generators for the horizontal heat operator

The single-block heat operator has drift minus the time derivative. The two-block
operator has drift minus twice the time derivative and both spatial field families.
-/

@[expose] public section

noncomputable section

namespace HeatKernel

open RothschildStein Hormander.Interface

/-- Spacetime generators for the horizontal heat operator. -/
def horizontalHeatFields {n q : ℕ} (G : HomogeneousGroup n) (hq : q ≤ n) :=
  timeSpaceFields (-1) (G.horizontalFields hq)

/-- Spacetime generators for the sum of the two spatial heat operators. -/
def horizontalTwoSpaceHeatFields {n q : ℕ} (G : HomogeneousGroup n) (hq : q ≤ n) :=
  timeSpaceFields (-2) (sumFields (G.horizontalFields hq) (G.horizontalFields hq))

theorem contDiff_horizontalHeatFields {n q : ℕ} (G : HomogeneousGroup n) (hq : q ≤ n)
    (i : Fin (q + 1)) : ContDiff ℝ (⊤ : ℕ∞) (horizontalHeatFields G hq i) :=
  contDiff_timeSpaceFields (-1) _ (G.horizontalFields_contDiff hq) i

theorem contDiff_horizontalTwoSpaceHeatFields {n q : ℕ} (G : HomogeneousGroup n)
    (hq : q ≤ n) (i : Fin ((q + q) + 1)) :
    ContDiff ℝ (⊤ : ℕ∞) (horizontalTwoSpaceHeatFields G hq i) :=
  contDiff_timeSpaceFields (-2) _
    (contDiff_sumFields _ _ (G.horizontalFields_contDiff hq) (G.horizontalFields_contDiff hq)) i

/-- The original group bracket condition supplies all single-block spacetime directions. -/
theorem lieAlgebraSpansOn_horizontalHeatFields {n q : ℕ} (G : HomogeneousGroup n) (hq : q ≤ n)
    (hspan : bracketSpansOn Set.univ (G.horizontalFields hq)) :
    LieAlgebraSpansOn Set.univ (horizontalHeatFields G hq) :=
  lieAlgebraSpansOn_timeSpaceFields (by norm_num) _ (G.horizontalFields_contDiff hq) hspan

/-- The original group bracket condition supplies all two-block spacetime directions. -/
theorem lieAlgebraSpansOn_horizontalTwoSpaceHeatFields {n q : ℕ}
    (G : HomogeneousGroup n) (hq : q ≤ n)
    (hspan : bracketSpansOn Set.univ (G.horizontalFields hq)) :
    LieAlgebraSpansOn Set.univ (horizontalTwoSpaceHeatFields G hq) :=
  lieAlgebraSpansOn_timeTwoSpaceFields (by norm_num) _ (G.horizontalFields_contDiff hq) hspan

end HeatKernel
