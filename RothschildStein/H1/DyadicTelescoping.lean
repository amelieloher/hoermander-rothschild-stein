-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.KernelScaling

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open scoped BigOperators
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Exact telescoping of the scaled fundamental kernels before
passing to the smooth dyadic series (BB (6.27)–(6.28), pp. 265–266). -/
theorem scaledFundamentalKernel_dyadic_telescope
    (Γ : (Fin N → ℝ) → ℝ) (n : ℕ) (x : Fin N → ℝ) :
    scaledFundamentalKernel G ((2 : ℝ) ^ n) Γ x = Γ x +
      ∑ j ∈ Finset.range n, scaledFundamentalKernel G ((2 : ℝ) ^ j)
        (fun y => scaledFundamentalKernel G 2 Γ y - Γ y) x := by
  induction n with
  | zero => simp [scaledFundamentalKernel, G2.dilate_one]
  | succ n ih =>
      have H := scaledFundamentalKernel_double_sub G ((2 : ℝ) ^ n) Γ x
      rw [mul_comm 2, ← pow_succ, ih] at H
      rw [Finset.sum_range_succ]
      linarith

end RothschildStein.H1
