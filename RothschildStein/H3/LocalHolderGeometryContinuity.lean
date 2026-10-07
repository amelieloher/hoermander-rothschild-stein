-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Definitions.memHolderXLoc
public import RothschildStein.S.HolderSubsetContinuity
public import Mathlib.Geometry.Manifold.PartitionOfUnity

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped ENNReal
namespace RothschildStein.H3

/-- Local fixed Holder membership determines a continuous pointwise
representative for any of the shared distance geometries. -/
theorem continuousOn_of_memHolderXLoc_with_geometry {N m : ℕ}
    (w : Fin m → ℕ+) (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (D : S.DistanceGeometry (⊤ : Opens (Fin N → ℝ)))
    (Ω : Opens (Fin N → ℝ)) (k : ℕ) {α : ℝ} (ha : 0 < α)
    {u : (Fin N → ℝ) → ℝ} (hu : memHolderXLoc w X D.d Ω k α u) :
    ContinuousOn u (Ω : Set (Fin N → ℝ)) := by
  intro x hx
  obtain ⟨U, hU, hxU, hclU, hcU⟩ := exists_open_between_and_isCompact_closure
    (isCompact_singleton (x := x)) Ω.isOpen (singleton_subset_iff.mpr hx)
  let V : Opens (Fin N → ℝ) := ⟨U, hU⟩
  have hv := S.continuousOn_of_holderENorm_lt_top_on_subset ⊤ D
    (subset_univ _) ha (hu V hcU hclU).1
  exact (hv.continuousAt (hU.mem_nhds (hxU (mem_singleton x)))).continuousWithinAt

end RothschildStein.H3
