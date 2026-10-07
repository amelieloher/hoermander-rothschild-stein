-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Definitions.memSobolevXLoc
public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.Topology.Compactness.LocallyCompact

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set TopologicalSpace

/-- Every open coordinate domain has an increasing exhaustion
by relatively compact open patches with a support buffer at each step.
Every compact subset is contained in one patch. -/
theorem exists_relcompact_open_exhaustion {n : ℕ} (Ω : Opens (Fin n → ℝ)) :
    ∃ U : ℕ → Opens (Fin n → ℝ), Monotone U ∧
      (∀ k, IsCompact (closure (U k : Set (Fin n → ℝ))) ∧
        closure (U k : Set (Fin n → ℝ)) ⊆ U (k + 1) ∧ U k ≤ Ω) ∧
      (∀ x ∈ (Ω : Set (Fin n → ℝ)), ∃ k, x ∈ U k) ∧
      ∀ s : Set (Fin n → ℝ), IsCompact s → s ⊆ Ω → ∃ k, s ⊆ U k := by
  let lcΩ : LocallyCompactSpace (Ω : Set (Fin n → ℝ)) :=
    Ω.isOpen.isOpenEmbedding_subtypeVal.locallyCompactSpace
  let K : CompactExhaustion (Ω : Set (Fin n → ℝ)) := CompactExhaustion.choice _
  let U : ℕ → Opens (Fin n → ℝ) := fun k =>
    ⟨Subtype.val '' interior (K k), Ω.isOpen.isOpenMap_subtype_val _ isOpen_interior⟩
  have hmono : Monotone U := by
    intro i j hij
    exact image_mono (interior_mono (K.subset hij))
  have hUk (k : ℕ) : IsCompact (closure (U k : Set (Fin n → ℝ))) ∧
      closure (U k : Set (Fin n → ℝ)) ⊆ U (k + 1) ∧ U k ≤ Ω := by
    have hc : IsCompact (Subtype.val '' K k : Set (Fin n → ℝ)) :=
      (K.isCompact k).image continuous_subtype_val
    have hcl : closure (U k : Set (Fin n → ℝ)) ⊆ Subtype.val '' K k :=
      closure_minimal (image_mono interior_subset) hc.isClosed
    refine ⟨hc.of_isClosed_subset isClosed_closure hcl,
      hcl.trans (image_mono (K.subset_interior_succ k)), ?_⟩
    rintro x ⟨y, _, rfl⟩
    exact y.property
  have hcover : ∀ x ∈ (Ω : Set (Fin n → ℝ)), ∃ k, x ∈ U k := by
    intro x hx
    obtain ⟨k, hk⟩ := K.exists_mem ⟨x, hx⟩
    exact ⟨k + 1, ⟨⟨x, hx⟩, K.subset_interior_succ k hk, rfl⟩⟩
  refine ⟨U, hmono, hUk, hcover, ?_⟩
  intro s hs hsΩ
  exact hs.elim_directed_cover (fun k => (U k : Set (Fin n → ℝ)))
    (fun k => (U k).isOpen)
    (fun x hx => mem_iUnion.mpr (hcover x (hsΩ hx))) hmono.directed_le

end RothschildStein.H3
