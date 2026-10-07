-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Topology.Compactness.LocallyFinite

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
open scoped BigOperators Manifold
namespace RothschildStein.Distribution

/-- expose the ordinary smooth-function data of a
partition around a compact test support, with centers in that support. -/
theorem exists_smooth_partition_on_compact {N : ℕ}
    (K : Set (Fin N → ℝ)) (hK : IsCompact K)
    (U : (Fin N → ℝ) → Set (Fin N → ℝ))
    (hU : ∀ x ∈ K, U x ∈ nhds x) :
    ∃ (ι : Type) (ρ : ι → (Fin N → ℝ) → ℝ) (c : ι → (Fin N → ℝ)),
      LocallyFinite (fun i => Function.support (ρ i)) ∧
      (∀ x ∈ K, ∑ᶠ i, ρ i x = 1) ∧
      (∀ i, ContDiff ℝ (⊤ : ℕ∞) (ρ i)) ∧
      (∀ i, c i ∈ K) ∧ (∀ i, tsupport (ρ i) ⊆ U (c i)) := by
  obtain ⟨ι, b, hb⟩ := SmoothBumpCovering.exists_isSubordinate (𝓘(ℝ, Fin N → ℝ)) hK.isClosed hU
  let ρ := b.toSmoothPartitionOfUnity
  refine ⟨ι, fun i x => ρ i x, b.c, ρ.locallyFinite, fun x hx => ρ.sum_eq_one hx, ?_, b.c_mem', ?_⟩
  · intro i
    exact contMDiff_iff_contDiff.mp (ρ i).contMDiff
  · exact hb.toSmoothPartitionOfUnity

end RothschildStein.Distribution
