-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.LocalPowerFactorLeadingJet

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter
open scoped Topology BigOperators
namespace RothschildStein.G1

/-- An exact smooth local time-power factor has every lower
scalar jet zero (BB Lemma 1.52, pp. 30–31). -/
theorem local_power_factor_lower_jets {k j : ℕ} {G H : ℝ → ℝ}
    (hH : ContDiffAt ℝ j H 0) (hj : j < k)
    (he : G =ᶠ[𝓝 0] (fun t => t ^ k * H t)) : iteratedDeriv j G 0 = 0 := by
  rw [he.iteratedDeriv_eq j]
  have hp : ContDiffAt ℝ j (fun t : ℝ => t ^ k) 0 := (contDiff_id.pow k).contDiffAt
  rw [iteratedDeriv_fun_mul hp hH]
  apply Finset.sum_eq_zero
  intro i hi
  have hi' : i < j + 1 := Finset.mem_range.mp hi
  have hki : k - i ≠ 0 := by omega
  simp only [iteratedDeriv_pow, zero_pow hki, mul_zero, zero_mul]

end RothschildStein.G1
