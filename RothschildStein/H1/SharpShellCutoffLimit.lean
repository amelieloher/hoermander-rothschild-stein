-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.SharpShellCutoffSequence
public import RothschildStein.H1.ShellGeometry

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace RothschildStein.H1
variable {N : ℕ}

/-- Step 3: each sharp cutoff converges to the open unit-ball indicator. -/
theorem tendsto_sharpShellCutoff_value
    {ν : (Fin N → ℝ) → ℝ} {η : ℕ → (Fin N → ℝ) → ℝ}
    (hi : ∀ n x, ν x ≤ 1 - (1 / 2 : ℝ) ^ (n + 1) → η n x = 1)
    (ho : ∀ n x, 1 ≤ ν x → η n x = 0)
    (x : Fin N → ℝ) :
    Tendsto (fun n => η n x) atTop (𝓝 (if ν x < 1 then 1 else 0)) := by
  by_cases hlt : ν x < 1
  · rw [ite_eq_left hlt]
    apply tendsto_const_nhds.congr'
    filter_upwards [tendsto_sharpShell_innerRadius.eventually (lt_mem_nhds hlt)] with n hn
    exact (hi n x hn.le).symm
  · rw [ite_eq_right hlt]
    have he : (fun n => η n x) = fun _ : ℕ => (0 : ℝ) := by
      funext n
      exact ho n x (le_of_not_gt hlt)
    rw [he]
    exact tendsto_const_nhds

/-- Step 3: cutoff differences are dominated by the fixed
shell [r/2,R]. This makes the dominating kernel integrable. -/
theorem sharpShellCutoff_difference_bound (G : HomogeneousGroup N)
    {ν : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    {η : ℕ → (Fin N → ℝ) → ℝ}
    (hb : ∀ n x, 0 ≤ η n x ∧ η n x ≤ 1)
    (hi : ∀ n x, ν x ≤ 1 - (1 / 2 : ℝ) ^ (n + 1) → η n x = 1)
    (ho : ∀ n x, 1 ≤ ν x → η n x = 0)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) (n : ℕ) (x : Fin N → ℝ) :
    ‖η n (G.dilate R⁻¹ x) - η n (G.dilate r⁻¹ x)‖ ≤
      (gaugeShell ν (r / 2) R).indicator (fun _ => (1 : ℝ)) x := by
  have hR : 0 < R := hr.trans hrR
  have hscale (ρ : ℝ) (hρ : 0 < ρ) : ρ * ν (G.dilate ρ⁻¹ x) = ν x := by
    rw [hν.2.2.2 _ (inv_pos.mpr hρ), ← mul_assoc, mul_inv_cancel₀ hρ.ne', one_mul]
  have hvR := hscale R hR
  have hvr := hscale r hr
  by_cases hx : x ∈ gaugeShell ν (r / 2) R
  · rw [indicator_of_mem hx, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [(hb n (G.dilate R⁻¹ x)).1, (hb n (G.dilate r⁻¹ x)).2],
      by linarith [(hb n (G.dilate R⁻¹ x)).2, (hb n (G.dilate r⁻¹ x)).1]⟩
  · rw [indicator_of_notMem hx]
    have hx' : ν x < r / 2 ∨ R < ν x := by
      simp only [gaugeShell, mem_ofPred_eq, not_and_or, not_le] at hx
      exact hx
    rcases hx' with hx' | hx'
    · have hvalR : ν (G.dilate R⁻¹ x) ≤ 1 / 2 := by nlinarith
      have hvalr : ν (G.dilate r⁻¹ x) ≤ 1 / 2 := by nlinarith
      rw [hi n _ (hvalR.trans (sharpShell_innerRadius_ge_half n)),
        hi n _ (hvalr.trans (sharpShell_innerRadius_ge_half n)), sub_self, norm_zero]
    · have hvalR : 1 ≤ ν (G.dilate R⁻¹ x) := by nlinarith
      have hvalr : 1 ≤ ν (G.dilate r⁻¹ x) := by nlinarith
      rw [ho n _ hvalR, ho n _ hvalr, sub_self, norm_zero]

end RothschildStein.H1
