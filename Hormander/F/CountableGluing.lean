-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.F.PatchChoice
public import Mathlib.Topology.Compactness.Lindelof

@[expose] public section

noncomputable section

open Filter MeasureTheory Set Topology

namespace Hormander.F

/-- Local almost-everywhere identities combine to an identity on
an open set by taking a countable subcover. -/
theorem countable_local_ae_gluing {N : ℕ} {Ω : Set (Fin N → ℝ)} (hΩ : IsOpen Ω)
    {ι : Type*} (U : ι → Set (Fin N → ℝ))
    (f : ι → (Fin N → ℝ) → ℝ) (u : (Fin N → ℝ) → ℝ)
    (hUopen : ∀ i, IsOpen (U i)) (hUsub : ∀ i, U i ⊆ Ω)
    (hcover : ∀ x ∈ Ω, ∃ i, x ∈ U i)
    (hf : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (f i) (U i))
    (hae : ∀ i, f i =ᵐ[volume.restrict (U i)] u) :
    ∀ᵐ x ∂volume, x ∈ Ω → patchChoice Ω U f hcover x = u x := by
  have hchoice := patch_choice_smoothness hΩ U f u hUopen hUsub hcover hf hae
  let W : ι → Set Ω := fun i => {x | (x : Fin N → ℝ) ∈ U i}
  have hWopen : ∀ i, IsOpen (W i) := fun i => (hUopen i).preimage continuous_subtype_val
  have hWcover : (Set.univ : Set Ω) ⊆ ⋃ i, W i := by
    intro x hx
    obtain ⟨i, hi⟩ := hcover x.1 x.2
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨T, hTcountable, hTcover⟩ :=
    (isLindelof_univ : IsLindelof (Set.univ : Set Ω)).elim_countable_subcover
      W hWopen hWcover
  have : Countable T := hTcountable.to_subtype
  have hlocal (i : ι) : ∀ᵐ x ∂volume, x ∈ U i → patchChoice Ω U f hcover x = u x := by
    have hselectedAmbient : ∀ᵐ x ∂volume,
        x ∈ U i → patchChoice Ω U f hcover x = f i x :=
      Filter.Eventually.of_forall (fun x hx => hchoice.2 i hx)
    have hselected : patchChoice Ω U f hcover =ᵐ[volume.restrict (U i)] f i :=
      (ae_restrict_iff' (hUopen i).measurableSet).2 hselectedAmbient
    have hEq := hselected.trans (hae i)
    exact (ae_restrict_iff' (hUopen i).measurableSet).mp hEq
  have hlocalCountable : ∀ᵐ x ∂volume,
      ∀ i : T, x ∈ U i.1 → patchChoice Ω U f hcover x = u x := by
    rw [ae_all_iff]
    intro i
    exact hlocal i.1
  filter_upwards [hlocalCountable] with x hx
  intro hxΩ
  obtain ⟨i, hiT, hxi⟩ := by
    let y : Ω := ⟨x, hxΩ⟩
    have hsubtype : y ∈ ⋃ i ∈ T, W i := hTcover (Set.mem_univ y)
    simpa only [Set.mem_iUnion, exists_prop] using hsubtype
  exact hx ⟨i, hiT⟩ hxi

end Hormander.F
