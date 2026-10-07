-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.TypeCalculusStatements
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
open scoped BigOperators
namespace RothschildStein.P1

/-- Finite principal weak outputs may be
reassembled into basis rows and the complete error row, preserving
all list multiplicities. -/
theorem transferFiniteSum_reassemble {A J : Type*} [Fintype J]
    (l : List A) (f : A → J → ℝ) (e : A → ℝ) (r : J → ℝ) (er : ℝ) :
    (l.map (fun a => (∑ j, f a j) + e a)).sum + ((∑ j, r j) + er) =
      (∑ j, ((l.map (fun a => f a j)).sum + r j)) + (l.map e).sum + er := by
  induction l with
  | nil => simp only [List.map_nil, List.sum_nil, zero_add, add_zero]
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    simp_rw [show ∀ j, f a j + (l.map (fun a => f a j)).sum + r j =
      f a j + ((l.map (fun a => f a j)).sum + r j) by intro j; ring]
    rw [Finset.sum_add_distrib]
    linear_combination ih

end RothschildStein.P1
