-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.SmoothShellCutoff
public import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Step 3: actual smooth sharp-shell cutoffs, using inner
radii 1 − 2⁻⁽ⁿ⁺¹⁾. No differentiability of the gauge is required. -/
theorem exists_sharpShellCutoff_sequence {ν : (Fin N → ℝ) → ℝ}
    (hν : G.IsHomogeneousGauge ν) :
    ∃ η : ℕ → (Fin N → ℝ) → ℝ, ∀ n,
      ContDiff ℝ (⊤ : ℕ∞) (η n) ∧ HasCompactSupport (η n) ∧
      (∀ x, 0 ≤ η n x ∧ η n x ≤ 1) ∧
      (∀ x, ν x ≤ 1 - (1 / 2 : ℝ) ^ (n + 1) → η n x = 1) ∧
      (∀ x, 1 ≤ ν x → η n x = 0) := by
  have he (n : ℕ) := exists_smoothShellCutoff G hν
    (a := 1 - (1 / 2 : ℝ) ^ (n + 1))
    (sub_lt_self 1 (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) _))
  exact ⟨fun n => Classical.choose (he n), fun n => Classical.choose_spec (he n)⟩

/-- The inner cutoff radii tend to one. -/
theorem tendsto_sharpShell_innerRadius :
    Tendsto (fun n : ℕ => 1 - (1 / 2 : ℝ) ^ (n + 1)) atTop (𝓝 1) := by
  have hp : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub (hp.mul_const (1 / 2 : ℝ))
  simpa only [pow_succ, zero_mul, sub_zero] using h

/-- Each sharp-shell inner radius is at least one half. -/
theorem sharpShell_innerRadius_ge_half (n : ℕ) :
    (1 / 2 : ℝ) ≤ 1 - (1 / 2 : ℝ) ^ (n + 1) := by
  have hp : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  rw [pow_succ]
  nlinarith

end RothschildStein.H1
