-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.IntrinsicNormRepresentatives
public import RothschildStein.S.Sobolev
public import RothschildStein.Definitions.holderXENorm

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped ENNReal BigOperators
namespace RothschildStein.H3

/-- Compatible actual intrinsic jets realize the full fixed
weighted Hölder norm as the finite sum of their scalar norms. -/
theorem holderXENorm_eq_sum_intrinsic_jets {N m : ℕ}
    (w : Fin m → ℕ+) (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (d : (Fin N → ℝ) → (Fin N → ℝ) → ℝ≥0∞)
    (U : Opens (Fin N → ℝ)) (k : ℕ) (α : ℝ) (u : (Fin N → ℝ) → ℝ)
    (jet : List (Fin m) → (Fin N → ℝ) → ℝ)
    (hj : ∀ I, wordWeight w I ≤ k → hasIntrinsicWordDeriv X U I u (jet I)) :
    holderXENorm w X d U k α u =
      ∑ I ∈ wordFamily w k, holderENorm d α (U : Set (Fin N → ℝ)) (jet I) := by
  unfold holderXENorm
  apply Finset.sum_congr rfl
  intro I hI
  exact S.intrinsicWordENorm_eq_representative U X d I α u (jet I)
    (hj I ((S.mem_wordFamily_iff w k I).mp hI))

/-- A common scalar bound for all intrinsic jets gives the
full fixed bound with the exact finite word count. -/
theorem holderXENorm_le_card_mul_of_intrinsic_jets {N m : ℕ}
    (w : Fin m → ℕ+) (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (d : (Fin N → ℝ) → (Fin N → ℝ) → ℝ≥0∞)
    (U : Opens (Fin N → ℝ)) (k : ℕ) (α : ℝ) (u : (Fin N → ℝ) → ℝ)
    (jet : List (Fin m) → (Fin N → ℝ) → ℝ)
    (hj : ∀ I, wordWeight w I ≤ k → hasIntrinsicWordDeriv X U I u (jet I))
    (M : ℝ≥0∞) (hb : ∀ I, wordWeight w I ≤ k →
      holderENorm d α (U : Set (Fin N → ℝ)) (jet I) ≤ M) :
    holderXENorm w X d U k α u ≤ (wordFamily w k).card * M := by
  rw [holderXENorm_eq_sum_intrinsic_jets w X d U k α u jet hj]
  calc
    _ ≤ ∑ _I ∈ wordFamily w k, M :=
      Finset.sum_le_sum (fun I hI => hb I ((S.mem_wordFamily_iff w k I).mp hI))
    _ = _ := by simp

end RothschildStein.H3
