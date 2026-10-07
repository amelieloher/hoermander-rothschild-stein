-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.WeakIntrinsicWords
public import RothschildStein.S.WeakHolderRepresentatives
public import RothschildStein.S.HolderSubsetContinuity
public import RothschildStein.Definitions.memHolderX

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.S
variable {n q : ℕ}

/-- The internal weak weighted Hölder class embeds
in the exact intrinsic class, on each open subdomain using
the fixed ambient distance (BB Definition 2.13 and Proposition 2.22, pp. 81, 87–90). -/
theorem memHolderX_of_memWeakHolderX
    (Ω U : Opens (Fin n → ℝ)) (G : DistanceGeometry Ω)
    (hU : (U : Set (Fin n → ℝ)) ⊆ Ω) (w : Fin q → ℕ+)
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i,ContDiffOn ℝ (⊤ : ℕ∞) (X i) (U : Set (Fin n → ℝ)))
    (k : ℕ) {α : ℝ} (hα : 0 < α) {f : (Fin n → ℝ) → ℝ}
    (hf : memWeakHolderX w X G.d U k α f) : memHolderX w X G.d U k α f := by
  obtain ⟨jet,hzero,hjet⟩ := exists_weakHolder_representatives w X G.d U k α hf
  refine ⟨hf.1,fun I hI => ?_⟩
  have hs : ∀ J,J.Sublist I → J ∈ wordFamily w k := by
    intro J hJ
    exact (mem_wordFamily_iff w k J).mpr
      ((wordWeight_sublist_le w hJ).trans ((mem_wordFamily_iff w k I).mp hI))
  exact ⟨jet I,hasIntrinsicWordDeriv_of_continuous_weak_subwords U X hX I f jet hzero
    (fun J hJ => (hjet J (hs J hJ)).1)
    (fun J hJ => continuousOn_of_holderENorm_lt_top_subset Ω G hU hα (hjet J (hs J hJ)).2),
    (hjet I hI).2⟩

end RothschildStein.S
