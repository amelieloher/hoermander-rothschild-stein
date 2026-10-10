-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.CoverChain

/-! Simple chains in open covers of connected path images. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace HeatKernel

/-- Any two members of an open cover that meet the image of a continuous map from a
preconnected space are joined by a finite simple intersection chain. -/
theorem exists_simple_chain_of_preconnected_image_cover {E T ι : Type*}
    [TopologicalSpace E] [TopologicalSpace T] [PreconnectedSpace T]
    (U : ι → Set E) (hopen : ∀ i, IsOpen (U i))
    (γ : T → E) (hγ : Continuous γ) (hcover : ∀ t, ∃ i, γ t ∈ U i)
    (i j : ι) (hi : ∃ t, γ t ∈ U i) (hj : ∃ t, γ t ∈ U j) :
    ∃ p : (intersectionGraph U).Walk i j, p.IsPath := by
  classical
  have he : (⋃ a, γ ⁻¹' U a) = univ := by
    apply eq_univ_iff_forall.mpr
    intro t
    obtain ⟨a, ha⟩ := hcover t
    exact mem_iUnion.mpr ⟨a, ha⟩
  have hc : IsPreconnected (⋃ a, γ ⁻¹' U a) := by rw [he]; exact isPreconnected_univ
  have ht := hc.transGen_of_iUnion (fun a => (hopen a).preimage hγ) i j hi hj
  have hstep : ∀ a b, ((γ ⁻¹' U a) ∩ (γ ⁻¹' U b)).Nonempty →
      (intersectionGraph U).Reachable a b := by
    rintro a b ⟨t, hta, htb⟩
    by_cases hab : a = b
    · subst b
      exact SimpleGraph.Reachable.refl a
    · exact SimpleGraph.Adj.reachable (G := intersectionGraph U) ⟨hab, γ t, hta, htb⟩
  clear hi hj
  have hr : (intersectionGraph U).Reachable i j := by
    induction ht with
    | single h => exact hstep _ _ h
    | tail _ h ih => exact ih.trans (hstep _ _ h)
  exact hr.exists_isPath

end HeatKernel
