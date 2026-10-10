-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueBoundedPowers
import Mathlib.Tactic

/-! # Chain factors and limits for bounded positive powers -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace HeatKernel

/-- For each nonnegative value the bounded powers are eventually the full power. -/
theorem eventually_boundedPositivePower_eq_rpow {γ s : ℝ} (hs : 0 ≤ s) :
    ∀ᶠ n : ℕ in atTop, boundedPositivePower ((n : ℝ) + 1) γ s = s ^ γ := by
  obtain ⟨N, hN⟩ := exists_nat_ge s
  filter_upwards [eventually_ge_atTop N] with n hn
  apply boundedPositivePower_eq_rpow hs
  have hcast : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
  linarith

end HeatKernel
