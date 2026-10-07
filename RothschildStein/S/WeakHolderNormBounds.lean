-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.WeakHolderNorm
public import RothschildStein.S.WeakHolderRepresentatives
public import RothschildStein.S.HolderZeroOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped ENNReal BigOperators
namespace RothschildStein.S
variable {n q : ℕ}

/-- The internal weak norm is the finite sum of the scalar norms of any finite Hölder weak word family (BB Def 2.13,
p. 81; norm assembly). -/
theorem weakHolderXENorm_eq_sum_representatives
    (Ω U : Opens (Fin n → ℝ)) (G : DistanceGeometry Ω)
    (hU : (U : Set (Fin n → ℝ)) ⊆ Ω) (w : Fin q → ℕ+)
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)) (k : ℕ)
    {α : ℝ} (hα : 0 < α) (f : (Fin n → ℝ) → ℝ)
    (jet : List (Fin q) → (Fin n → ℝ) → ℝ)
    (hj : ∀ I ∈ wordFamily w k,hasWeakWordDeriv X U I f (jet I) ∧
      holderENorm G.d α (U : Set (Fin n → ℝ)) (jet I) < ⊤) :
    weakHolderXENorm w X G.d U k α f =
      ∑ I ∈ wordFamily w k,holderENorm G.d α (U : Set (Fin n → ℝ)) (jet I) := by
  unfold weakHolderXENorm
  apply Finset.sum_congr rfl
  intro I hI
  exact weakHolderWordENorm_eq Ω U G hU X I hα f (jet I) (hj I hI).1 (hj I hI).2

end RothschildStein.S
