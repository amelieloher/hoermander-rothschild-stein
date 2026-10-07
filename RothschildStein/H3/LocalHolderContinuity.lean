-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Definitions.driftWeight
public import RothschildStein.H3.ControlDistanceGeometry
public import RothschildStein.H1.Standing
public import RothschildStein.Definitions.memHolderXLoc
public import RothschildStein.S.HolderSubsetContinuity
public import Mathlib.Geometry.Manifold.PartitionOfUnity

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped ENNReal NNReal
namespace RothschildStein.H3

/-- Literal local fixed Holder membership gives continuity
on the original open domain, including its pointwise representative. -/
theorem continuousOn_of_memHolderXLoc_of_controlNorm {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (C : G2.ControlNormConclusion G driftWeight H.fields)
    (Ω : Opens (Fin N → ℝ)) (k : ℕ) {a : ℝ≥0} (ha : 0 < a)
    {u : (Fin N → ℝ) → ℝ}
    (hu : memHolderXLoc driftWeight H.fields (controlDistance univ driftWeight H.fields) Ω k a u) :
    ContinuousOn u (Ω : Set (Fin N → ℝ)) := by
  let D := controlDistanceGeometry_of_controlNorm G driftWeight H.fields C
  intro x hx
  obtain ⟨U, hU, hxU, hclU, hcU⟩ := exists_open_between_and_isCompact_closure
    (isCompact_singleton (x := x)) Ω.isOpen (singleton_subset_iff.mpr hx)
  let V : Opens (Fin N → ℝ) := ⟨U, hU⟩
  have hv := RothschildStein.S.continuousOn_of_holderENorm_lt_top_on_subset ⊤ D
    (subset_univ _) (show 0 < (a : ℝ) from ha) (hu V hcU hclU).1
  exact (hv.continuousAt (hU.mem_nhds (hxU (mem_singleton x)))).continuousWithinAt

end RothschildStein.H3
