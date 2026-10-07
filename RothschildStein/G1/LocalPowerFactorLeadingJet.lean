-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.CoordinatePowerFactor

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter
open scoped BigOperators Topology

namespace RothschildStein.G1

/-- The leading jet identifies a smooth factor on its actual
local domain; only a germ identity and finite smoothness at zero are
needed (BB Lemma 1.52, pp. 30–31). -/
theorem local_power_factor_leading_jet {k : ℕ} {G H : ℝ → ℝ}
    (hH : ContDiffAt ℝ k H 0)
    (he : G =ᶠ[𝓝 0] (fun t => t ^ k * H t)) :
    iteratedDeriv k G 0 = (k.factorial : ℝ) * H 0 := by
  rw [he.iteratedDeriv_eq k]
  have hp : ContDiffAt ℝ k (fun t : ℝ => t ^ k) 0 :=
    (contDiff_id.pow k).contDiffAt
  rw [iteratedDeriv_fun_mul hp hH, Finset.sum_eq_single k]
  · simp [iteratedDeriv_pow, Nat.descFactorial_self]
  · intro i hi hik
    have hi' : i < k + 1 := Finset.mem_range.mp hi
    have hdiff : k - i ≠ 0 := by omega
    simp only [iteratedDeriv_pow, zero_pow hdiff, mul_zero, zero_mul]
  · simp

end RothschildStein.G1
