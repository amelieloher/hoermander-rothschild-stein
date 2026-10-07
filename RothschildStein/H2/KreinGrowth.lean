-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Filter
open scoped Topology

namespace RothschildStein.H2

/-- The dyadic growth argument behind Krein's lemma.
BB (7.16)–(7.17), pp. 309–310, with powers instead of fractional exponents. -/
theorem krein_dyadic_growth {v : ℕ → ℝ} {B c : ℝ} (hv : ∀ j, 0 ≤ v j)
    (hc : 0 ≤ c) (hstep : ∀ j, v j ^ 2 ≤ v (j + 1))
    (hbound : ∀ j, v j ≤ B * c ^ (2 ^ j)) : v 0 ≤ c := by
  have hlower : ∀ j, v 0 ^ (2 ^ j) ≤ v j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc
        _ = (v 0 ^ (2 ^ j)) ^ 2 := by rw [pow_succ, pow_mul]
        _ ≤ v j ^ 2 := pow_le_pow_left₀ (pow_nonneg (hv 0) _) ih 2
        _ ≤ _ := hstep j
  rcases hc.eq_or_lt with rfl | hc
  · simpa using hbound 0
  by_contra hn
  have hratio : 1 < v 0 / c := (one_lt_div hc).mpr (lt_of_not_ge hn)
  have he : ∀ j, (v 0 / c) ^ (2 ^ j) ≤ B := by
    intro j
    rw [div_pow, div_le_iff₀ (pow_pos hc _)]
    exact (hlower j).trans (hbound j)
  have ht : Tendsto (fun j : ℕ => (v 0 / c) ^ (2 ^ j)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hratio).comp
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2))
  obtain ⟨j, hj⟩ := (ht.eventually (eventually_gt_atTop B)).exists
  exact (not_lt_of_ge (he j)) hj

end RothschildStein.H2
