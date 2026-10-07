-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Basic.ENNReal.Inv

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace RothschildStein.L1

/-- Two-sided real frame-scale bounds give two-sided actual
volume-ratio bounds. The complete numerator and denominator scales are
retained, including a small original determinant (BB pp. 521–522). -/
theorem measure_ratio_bounds_of_positive_real_scales {n N : ℕ}
    (A : Set (Fin n → ℝ)) (B : Set (Fin N → ℝ))
    {S T c₀ C₀ c₁ C₁ : ℝ} (hS : 0 < S)
    (hc₀ : 0 < c₀) (hC₀ : 0 < C₀) (hc₁ : 0 ≤ c₁) (hC₁ : 0 ≤ C₁)
    (hA : ENNReal.ofReal (c₀ * S) ≤ volume A ∧ volume A ≤ ENNReal.ofReal (C₀ * S))
    (hB : ENNReal.ofReal (c₁ * T) ≤ volume B ∧ volume B ≤ ENNReal.ofReal (C₁ * T)) :
    ENNReal.ofReal (c₁ / C₀) * ENNReal.ofReal (T / S) ≤ volume B / volume A ∧
      volume B / volume A ≤ ENNReal.ofReal (C₁ / c₀) * ENNReal.ofReal (T / S) := by
  have hl := ENNReal.div_le_div hB.1 hA.2
  have hu := ENNReal.div_le_div hB.2 hA.1
  have he₀ : ENNReal.ofReal (c₁ * T) / ENNReal.ofReal (C₀ * S) =
      ENNReal.ofReal (c₁ / C₀) * ENNReal.ofReal (T / S) := by
    rw [← ENNReal.ofReal_div_of_pos (mul_pos hC₀ hS),
      ← ENNReal.ofReal_mul (div_nonneg hc₁ hC₀.le)]
    congr 1
    ring
  have he₁ : ENNReal.ofReal (C₁ * T) / ENNReal.ofReal (c₀ * S) =
      ENNReal.ofReal (C₁ / c₀) * ENNReal.ofReal (T / S) := by
    rw [← ENNReal.ofReal_div_of_pos (mul_pos hc₀ hS),
      ← ENNReal.ofReal_mul (div_nonneg hC₁ hc₀.le)]
    congr 1
    ring
  exact ⟨he₀ ▸ hl, he₁ ▸ hu⟩

end RothschildStein.L1
