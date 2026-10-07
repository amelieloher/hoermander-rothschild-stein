-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.SharpShellCutoffLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Step 3: dilation makes the sharp cutoff converge to the
indicator of a gauge ball of any positive radius. -/
theorem tendsto_sharpShellCutoff_dilate
    {ν : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    {η : ℕ → (Fin N → ℝ) → ℝ}
    (hi : ∀ n x, ν x ≤ 1 - (1 / 2 : ℝ) ^ (n + 1) → η n x = 1)
    (ho : ∀ n x, 1 ≤ ν x → η n x = 0)
    {ρ : ℝ} (hρ : 0 < ρ) (x : Fin N → ℝ) :
    Tendsto (fun n => η n (G.dilate ρ⁻¹ x)) atTop
      (𝓝 (if ν x < ρ then 1 else 0)) := by
  have h := tendsto_sharpShellCutoff_value hi ho (G.dilate ρ⁻¹ x)
  have he : ν (G.dilate ρ⁻¹ x) < 1 ↔ ν x < ρ := by
    rw [hν.2.2.2 _ (inv_pos.mpr hρ), inv_mul_eq_div, div_lt_one hρ]
  simpa only [he] using h

end RothschildStein.H1
