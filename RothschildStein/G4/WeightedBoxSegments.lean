-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.WeightedBoxes
public import Mathlib.Analysis.Convex.Basic

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G4

/-- Coordinate contraction segments stay in their weighted box. -/
theorem convex_weightedBox {n : ℕ} (w : Fin n → ℕ+) (r : ℝ) :
    Convex ℝ (weightedBox w r) := by
  have heq : weightedBox w r = Set.pi Set.univ
      (fun i => Ioo (-r ^ (w i : ℕ)) (r ^ (w i : ℕ))) := by
    ext u
    simp only [weightedBox, mem_ofPred_eq, mem_pi, mem_univ, forall_true_left,
      mem_Ioo, abs_lt]
  rw [heq]
  exact convex_pi (fun i _ => convex_Ioo _ _)

/-- A segment velocity between two small-box points carries one
common small factor, independently of their positive coordinate weights. -/
theorem weightedBox_segment_velocity_bound {n : ℕ} (w : Fin n → ℕ+)
    {β r : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (hr : 0 ≤ r)
    {u v : Fin n → ℝ} (hu : u ∈ weightedBox w (β * r))
    (hv : v ∈ weightedBox w (β * r)) :
    ∀ i, |v i - u i| ≤ 2 * β * r ^ (w i : ℕ) := by
  intro i
  have hp : β ^ (w i : ℕ) ≤ β := pow_le_of_le_one hβ hβ1 (w i).ne_zero
  have htri : |v i - u i| ≤ |v i| + |u i| := by
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (v i) (-u i)
  have hi := htri.trans (add_le_add (hv i).le (hu i).le)
  rw [mul_pow] at hi
  exact hi.trans (by nlinarith [mul_le_mul_of_nonneg_right hp (pow_nonneg hr (w i : ℕ))])

end RothschildStein.G4
