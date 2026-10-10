-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Tactic

/-! # Absorption of the cutoff flux in logarithmic energy estimates -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory
namespace HeatKernel

/-- Positivity of the coefficient form absorbs the logarithmic cutoff cross term,
retaining half of the principal energy and twice the cutoff energy. -/
theorem logarithmic_energy_absorption {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hsym : ∀ v w, B v w = B w v)
    (hpos : ∀ v, 0 ≤ B v v) (η : ℝ) (v k : E) :
    η^2 * B v v / 2 - 2 * B k k ≤ η^2 * B v v - 2 * (η * B v k) := by
  have hp := hpos (η • v - (2 : ℝ) • k)
  have he : B (η • v - (2 : ℝ) • k) (η • v - (2 : ℝ) • k) =
      η^2 * B v v - 4 * η * B v k + 4 * B k k := by
    simp only [map_sub, map_smul, sub_apply,
      smul_apply, smul_eq_mul]
    rw [hsym k v]
    ring
  rw [he] at hp
  linarith

end HeatKernel
