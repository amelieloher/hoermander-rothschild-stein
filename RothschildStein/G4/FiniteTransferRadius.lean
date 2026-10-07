-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Logic.Function.Iterate

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace RothschildStein.G4

/-- Iterating a positive chart-radius shrinkage keeps every
intermediate radius in the positive unit interval (BB p. 458). -/
theorem transfer_radius_iterates_positive (f : ℝ → ℝ) {α : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hf : ∀ a : ℝ, 0 < a → a ≤ 1 → 0 < f a ∧ f a ≤ 1) :
    ∀ j : ℕ, 0 < f^[j] α ∧ f^[j] α ≤ 1 := by
  intro j
  induction j with
  | zero => exact ⟨hα, hα1⟩
  | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact hf _ ih.1 ih.2

/-- A bounded number of frame transfers has one positive
common injective-box radius. No monotonicity of the shrinkage map is needed;
take a minimum over the finitely many iteration depths (BB p. 458). -/
theorem exists_positive_finite_transfer_radius (f : ℝ → ℝ) {α : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hf : ∀ a : ℝ, 0 < a → a ≤ 1 → 0 < f a ∧ f a ≤ 1) (N : ℕ) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ j ≤ N, c ≤ f^[j] α := by
  have hi := transfer_radius_iterates_positive f hα hα1 hf
  induction N with
  | zero =>
      refine ⟨α, hα, hα1, ?_⟩
      intro j hj
      have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
      subst j
      exact le_rfl
  | succ N ih =>
      obtain ⟨c, hc, hc1, hcb⟩ := ih
      refine ⟨min c (f^[N + 1] α), lt_min hc (hi _).1,
        (min_le_left _ _).trans hc1, ?_⟩
      intro j hj
      by_cases hsmall : j ≤ N
      · exact (min_le_left _ _).trans (hcb j hsmall)
      · have hjlast : j = N + 1 := le_antisymm hj (Nat.succ_le_of_lt (Nat.lt_of_not_ge hsmall))
        subst j
        exact min_le_right _ _

end RothschildStein.G4
