-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Filter
open scoped Topology
namespace RothschildStein.H3

/-- A scaled full-norm estimate implies the
support-independent seminorm estimate by sending the scale to infinity.
The scaled estimate remains explicit (BB Corollary 8.51, p. 380). -/
theorem holder_seminorm_bound_of_scaled_full_norm_bound
    {α R0 A B S T C : ℝ} (hα : 0 < α) (hA : 0 ≤ A)
    (hscale : ∀ R : ℝ, R0 ≤ R → 0 < R → A + R ^ α * B ≤ C * (S + R ^ α * T)) :
    B ≤ C * T := by
  have hb : ∀ᶠ R : ℝ in atTop, B ≤ C * S * R ^ (-α) + C * T := by
    filter_upwards [eventually_ge_atTop R0, eventually_gt_atTop (0 : ℝ)] with R hR hpos
    have hp : 0 < R ^ α := Real.rpow_pos_of_pos hpos α
    have hh : R ^ α * B ≤ C * (S + R ^ α * T) :=
      (le_add_of_nonneg_left hA).trans (hscale R hR hpos)
    apply (mul_le_mul_iff_left₀ hp).mp
    have he : (C * S * R ^ (-α) + C * T) * R ^ α = C * (S + R ^ α * T) := by
      rw [Real.rpow_neg hpos.le]
      field_simp [hp.ne']
    calc
      B * R ^ α = R ^ α * B := mul_comm _ _
      _ ≤ C * (S + R ^ α * T) := hh
      _ = _ := he.symm
  have hl : Tendsto (fun R : ℝ => C * S * R ^ (-α) + C * T) atTop (𝓝 (C * T)) := by
    simpa only [mul_zero, zero_add] using
      ((tendsto_rpow_neg_atTop hα).const_mul (C * S)).add_const (C * T)
  exact ge_of_tendsto hl hb

end RothschildStein.H3
