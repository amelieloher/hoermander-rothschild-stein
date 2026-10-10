-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Data.Set.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-! # Separating-time logarithmic tails and centered oscillations -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace HeatKernel

/-- A bound for the linear time correction places the earlier upper tail inside
the centered oscillation tail with the decreasing corrected-mean deviation. -/
theorem earlier_logarithmic_tail_subset {α : Type*} (f : α → ℝ) (m : ℝ → ℝ)
    {C t τ ℓ : ℝ} (hshift : C * (τ - t) ≤ ℓ / 2) :
    {x | m τ + ℓ < f x} ⊆
      {x | ℓ / 2 + ((m τ + C * τ) - (m t + C * t)) < f x - m t} := by
  intro x hx
  change m τ + ℓ < f x at hx
  change ℓ / 2 + ((m τ + C * τ) - (m t + C * t)) < f x - m t
  nlinarith

/-- The corresponding correction bound places the later lower tail inside
the centered oscillation tail with the increasing corrected-mean deviation. -/
theorem later_logarithmic_tail_subset {α : Type*} (f : α → ℝ) (m : ℝ → ℝ)
    {C t τ ℓ : ℝ} (hshift : C * (t - τ) ≤ ℓ / 2) :
    {x | f x < m τ - ℓ} ⊆
      {x | ℓ / 2 + ((m t + C * t) - (m τ + C * τ)) < m t - f x} := by
  intro x hx
  change f x < m τ - ℓ at hx
  change ℓ / 2 + ((m t + C * t) - (m τ + C * τ)) < m t - f x
  nlinarith

end HeatKernel
