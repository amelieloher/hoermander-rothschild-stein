-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.WeakHolderToIntrinsic
public import RothschildStein.S.WeakHolderNormBounds
public import RothschildStein.S.IntrinsicNormRepresentatives
public import RothschildStein.Definitions.holderXENorm

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped ENNReal BigOperators
namespace RothschildStein.S
variable {n q : ℕ}

/-- On weak Hölder data the internal weak norm
is exactly the intrinsic full norm. Both norms are computed
by the same continuous word representatives (BB Def 2.13 and
Prop 2.22, pp. 81, 87–90). -/
theorem holderXENorm_eq_weakHolderXENorm
    (Ω U : Opens (Fin n → ℝ)) (G : DistanceGeometry Ω)
    (hU : (U : Set (Fin n → ℝ)) ⊆ Ω) (w : Fin q → ℕ+)
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i,ContDiffOn ℝ (⊤ : ℕ∞) (X i) (U : Set (Fin n → ℝ)))
    (k : ℕ) {α : ℝ} (hα : 0 < α) {f : (Fin n → ℝ) → ℝ}
    (hf : memWeakHolderX w X G.d U k α f) :
    holderXENorm w X G.d U k α f = weakHolderXENorm w X G.d U k α f := by
  obtain ⟨jet,hzero,hjet⟩ := exists_weakHolder_representatives w X G.d U k α hf
  rw [weakHolderXENorm_eq_sum_representatives Ω U G hU w X k hα f jet hjet]
  unfold holderXENorm
  apply Finset.sum_congr rfl
  intro I hI
  have hs : ∀ J,J.Sublist I → J ∈ wordFamily w k := by
    intro J hJ
    exact (mem_wordFamily_iff w k J).mpr
      ((wordWeight_sublist_le w hJ).trans ((mem_wordFamily_iff w k I).mp hI))
  exact intrinsicWordENorm_eq_representative U X G.d I α f (jet I)
    (hasIntrinsicWordDeriv_of_continuous_weak_subwords U X hX I f jet hzero
      (fun J hJ => (hjet J (hs J hJ)).1)
      (fun J hJ => continuousOn_of_holderENorm_lt_top_subset Ω G hU hα (hjet J (hs J hJ)).2))

end RothschildStein.S
