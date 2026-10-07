-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Definitions.hasIntrinsicWordDeriv

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.P1

/-- Intrinsic word derivatives commute with generator
reindexing, preserving the exact pointwise empty-word predicate. -/
theorem hasIntrinsicWordDeriv_map_indices_iff {a b n : ℕ}
    (X : Fin b → (Fin n → ℝ) → (Fin n → ℝ)) (e : Fin a → Fin b)
    (Ω : TopologicalSpace.Opens (Fin n → ℝ)) (I : List (Fin a))
    (f g : (Fin n → ℝ) → ℝ) :
    hasIntrinsicWordDeriv X Ω (I.map e) f g ↔
      hasIntrinsicWordDeriv (X ∘ e) Ω I f g := by
  induction I generalizing f g with
  | nil => rfl
  | cons i I ih =>
      simp only [List.map_cons, hasIntrinsicWordDeriv, Function.comp_apply, ih]

end RothschildStein.P1
