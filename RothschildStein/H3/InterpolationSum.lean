-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.InterpolationDensity

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
namespace RothschildStein.H3
open scoped ENNReal BigOperators

/-- Summing the one-field interpolation estimates gives the
 horizontal-family constants ε/2 and 2q/ε, including q=0. -/
theorem interpolation_sum_fields {q : ℕ} {ε : ℝ}
    (D DD : Fin q → ℝ≥0∞) (U : ℝ≥0∞)
    (h : ∀ i, D i ≤ ENNReal.ofReal (2/ε)*U + ENNReal.ofReal (ε/2)*DD i) :
    (∑ i, D i) ≤ ENNReal.ofReal (2*(q : ℝ)/ε)*U +
      ENNReal.ofReal (ε/2)*(∑ i, DD i) := by
  have hc : (q : ℝ≥0∞)*ENNReal.ofReal (2/ε) = ENNReal.ofReal (2*(q : ℝ)/ε) := by
    rw [← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (Nat.cast_nonneg q)]
    congr 1
    ring
  calc
    (∑ i, D i) ≤ ∑ i, (ENNReal.ofReal (2/ε)*U + ENNReal.ofReal (ε/2)*DD i) :=
      Finset.sum_le_sum fun i _ => h i
    _ = ENNReal.ofReal (2*(q : ℝ)/ε)*U + ENNReal.ofReal (ε/2)*(∑ i, DD i) := by
      rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
        nsmul_eq_mul,← Finset.mul_sum,← mul_assoc,hc]

end RothschildStein.H3
