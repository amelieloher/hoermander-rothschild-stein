-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.DriftSecondWordSum
public import RothschildStein.H3.FirstHolderNormFormula

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped ENNReal BigOperators
namespace RothschildStein.H3

/-- The fixed full weight-two norm is the complete
weight-one norm plus the drift and all ordered horizontal pair norms. -/
theorem holderXENorm_drift_two_split {N q : ℕ}
    (X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (d : (Fin N → ℝ) → (Fin N → ℝ) → ℝ≥0∞)
    (U : Opens (Fin N → ℝ)) (α : ℝ) (u : (Fin N → ℝ) → ℝ) :
    holderXENorm driftWeight X d U 2 α u = holderXENorm driftWeight X d U 1 α u +
      intrinsicWordENorm X d U [0] α u +
      ∑ i : Fin q, ∑ j : Fin q, intrinsicWordENorm X d U [i.succ, j.succ] α u := by
  classical
  have he : wordFamily (driftWeight (q := q)) 2 =
      wordFamily driftWeight 1 ∪ driftSecondWordFamily q := by
    ext I
    simp only [Finset.mem_union, S.mem_wordFamily_iff, mem_driftSecondWordFamily_iff]
    omega
  have hd : Disjoint (wordFamily (driftWeight (q := q)) 1) (driftSecondWordFamily q) := by
    apply Finset.disjoint_left.mpr
    intro I hI hJ
    have hi := (S.mem_wordFamily_iff driftWeight 1 I).mp hI
    have hj := (mem_driftSecondWordFamily_iff I).mp hJ
    omega
  unfold holderXENorm
  rw [he, Finset.sum_union hd, sum_driftSecondWordFamily]
  exact (add_assoc _ _ _).symm

end RothschildStein.H3
