-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.ChronologicalJetBounds
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace RothschildStein.G3

theorem chronologicalJetBudget_monotone (Q : ℕ) {B : ℝ} (hB : 1 ≤ B) :
    Monotone (chronologicalJetBudget Q B) := by
  apply monotone_nat_of_le_succ
  intro l
  have hprev : 0 ≤ chronologicalJetBudget Q B l :=
    zero_le_one.trans (chronologicalJetBudget_one_le Q B l)
  have hfact : (1 : ℝ) ≤ Q.factorial := by exact_mod_cast (show 1 ≤ Q.factorial by have := Nat.factorial_pos Q; omega)
  have hpow : (1 : ℝ) ≤ B^Q := one_le_pow₀ hB
  change chronologicalJetBudget Q B l ≤
    max 1 ((Q.factorial : ℝ)*chronologicalJetBudget Q B l*B^Q)
  apply le_trans _ (le_max_right _ _)
  calc
    chronologicalJetBudget Q B l ≤ (Q.factorial : ℝ)*chronologicalJetBudget Q B l :=
      le_mul_of_one_le_left hprev hfact
    _ ≤ (Q.factorial : ℝ)*chronologicalJetBudget Q B l*B^Q :=
      le_mul_of_one_le_right (mul_nonneg (by positivity) hprev) hpow
end RothschildStein.G3
