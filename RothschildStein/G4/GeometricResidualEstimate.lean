-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace RothschildStein.G4

/-- The higher-order endpoint error becomes a quarter-radius auxiliary residual
under the spanning-family Euclidean-to-control estimate. -/
theorem geometric_residual_rpow_le_quarter {s : ℕ} (hs : 0 < s)
    {E δ : ℝ} (hE : 0 ≤ E) (hδ : 0 ≤ δ)
    (hsmall : E * δ ≤ (1/4 : ℝ)^s) :
    (E * δ^(s+1)) ^ (1/(s : ℝ)) ≤ δ/4 := by
  rw [one_div]
  apply (Real.rpow_inv_le_iff_of_pos (by positivity) (by positivity)
    (by exact_mod_cast hs)).mpr
  rw [Real.rpow_natCast, div_pow, pow_succ]
  have hh := mul_le_mul_of_nonneg_right hsmall (pow_nonneg hδ s)
  rw [one_div_pow] at hh
  calc
    E * (δ^s*δ) = (E*δ)*δ^s := by ring
    _ ≤ (1/(4:ℝ)^s)*δ^s := hh
    _ = δ^s/(4:ℝ)^s := by ring
end RothschildStein.G4
