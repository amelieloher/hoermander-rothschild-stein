-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib
public import Mathlib.Algebra.Order.Archimedean.Basic

/-! Finite small-positive-power iteration up to a fixed endpoint exponent. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
namespace HeatKernel

/-- Geometric exponent growth reaches the endpoint in finitely many steps while
all tests through the last index remain below that endpoint. -/
theorem exists_reverse_holder_stopping_index {p p₀ χ : ℝ}
    (hp : 0 < p) (hpp₀ : p ≤ p₀) (hχ : 1 < χ) :
    ∃ n : ℕ, p * χ ^ n ≤ p₀ ∧ p₀ < p * χ ^ (n + 1) := by
  have hratio : 1 ≤ p₀ / p := (le_div_iff₀ hp).mpr (by simpa using hpp₀)
  obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near hratio hχ
  exact ⟨n, by nlinarith [(le_div_iff₀ hp).mp hn],
    by nlinarith [(div_lt_iff₀ hp).mp hn']⟩

end HeatKernel
