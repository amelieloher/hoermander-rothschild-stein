-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Topology.Connected.Basic

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set

namespace RothschildStein.G1

/-- An equivalence relation with locally reachable neighborhoods
has one class on a preconnected domain. This is the topological part of
Chow's argument, to be applied to actual finite generator paths
(BB Thm 1.45, p. 34). -/
theorem relation_universal_of_local_reachability {E : Type*} [TopologicalSpace E]
    {Ω : Set E} (hconn : IsPreconnected Ω) (R : E → E → Prop)
    (hrefl : ∀ x ∈ Ω, R x x)
    (hsymm : ∀ {x y}, R x y → R y x)
    (htrans : ∀ {x y z}, R x y → R y z → R x z)
    (hlocal : ∀ x ∈ Ω, ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ U ⊆ Ω ∧ ∀ y ∈ U, R x y)
    {x y : E} (hx : x ∈ Ω) (hy : y ∈ Ω) : R x y := by
  let C : Set E := {z | z ∈ Ω ∧ R x z}
  have hC : IsOpen C := isOpen_iff_mem_nhds.mpr (by
    intro z hz
    obtain ⟨U, hU, hzU, hUΩ, hR⟩ := hlocal z hz.1
    exact Filter.mem_of_superset (hU.mem_nhds hzU) (fun v hv => ⟨hUΩ hv, htrans hz.2 (hR v hv)⟩))
  have hD : IsOpen (Ω \ C) := isOpen_iff_mem_nhds.mpr (by
    intro z hz
    obtain ⟨U, hU, hzU, hUΩ, hR⟩ := hlocal z hz.1
    refine Filter.mem_of_superset (hU.mem_nhds hzU) ?_
    intro v hv
    refine ⟨hUΩ hv, ?_⟩
    intro hc
    exact hz.2 ⟨hz.1, htrans hc.2 (hsymm (hR v hv))⟩)
  have hdis : Disjoint C (Ω \ C) := by
    rw [Set.disjoint_left]
    exact fun _ hc hd => hd.2 hc
  have hcover : Ω ⊆ C ∪ (Ω \ C) := by
    intro z hz
    by_cases hc : z ∈ C
    · exact Or.inl hc
    · exact Or.inr ⟨hz, hc⟩
  rcases hconn.subset_or_subset hC hD hdis hcover with hall | hall
  · exact (hall hy).2
  · exact False.elim ((hall hx).2 ⟨hx, hrefl x hx⟩)

end RothschildStein.G1
