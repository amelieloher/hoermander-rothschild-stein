-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.WeightedJetAddition
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
open scoped BigOperators
namespace RothschildStein.L1

/-- Actual ordered partials distribute over finite sums on their smooth domain. -/
theorem rsPartial_finset_sum_on {N : ℕ} {ι : Type*}
    (Ω : Opens (Fin N → ℝ)) (T : Finset ι) (F : ι → (Fin N → ℝ) → ℝ)
    (hF : ∀ i ∈ T, ContDiffOn ℝ (⊤ : ℕ∞) (F i) Ω)
    (J : List (Fin N)) {x : Fin N → ℝ} (hx : x ∈ Ω) :
    rsPartial J (fun u => ∑ i ∈ T, F i u) x = ∑ i ∈ T, rsPartial J (F i) x := by
  classical
  revert hF
  induction T using Finset.induction_on with
  | empty => intro _; simp only [Finset.sum_empty, rsPartial_zero]
  | @insert i T hi ih =>
    intro hF
    simp only [Finset.sum_insert hi]
    have ht : ContDiffOn ℝ (⊤ : ℕ∞) (fun u => ∑ j ∈ T, F j u) Ω :=
      ContDiffOn.sum (fun j hj => hF j (by simp [hj]))
    rw [rsPartial_add_on Ω (F i) _ (hF i (by simp)) ht J hx,
      ih (fun j hj => hF j (by simp [hj]))]
end RothschildStein.L1
