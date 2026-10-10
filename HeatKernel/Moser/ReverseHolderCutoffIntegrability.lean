-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.NegativePowerFluxIntegrability

import all Mathlib.Basic.Real.Basic
import all Mathlib.Analysis.Normed.Group.Defs
import all Mathlib.Analysis.Normed.Group.Basic
import all Mathlib.Analysis.Normed.Group.Continuity
import all Mathlib.Analysis.Normed.Group.Real
import all Mathlib.Analysis.Normed.Field.Basic

/-! Square-integrable small powers multiplied by bounded cutoff gradients. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory
namespace HeatKernel

/-- A small nonnegative power times a bounded square-integrable cutoff
coordinate is square integrable when the original value is square integrable.
No nonlinear moment integrability is assumed. -/
theorem memLp_shifted_small_power_mul {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {u d : α → ℝ} {c r K : ℝ}
    (hc : 0 < c) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hu : MemLp u 2 μ) (hupos : ∀ᵐ x ∂μ, 0 ≤ u x)
    (hd : MemLp d 2 μ) (hdbound : ∀ᵐ x ∂μ, ‖d x‖ ≤ K) :
    MemLp (fun x => (u x + c) ^ r * d x) 2 μ := by
  have hprod : MemLp (fun x => d x * u x) 2 μ :=
    memLp_two_mul_of_ae_bound hd.aestronglyMeasurable hu hdbound
  have hdom : MemLp (fun x => ‖d x‖ + ‖d x * u x‖ + c * ‖d x‖) 2 μ := by
    simpa only [Pi.add_def, Pi.mul_def] using (hd.norm.add hprod.norm).add (hd.norm.const_mul c)
  apply hdom.mono'
    ((((hu.aestronglyMeasurable.add aestronglyMeasurable_const).aemeasurable.pow_const r).aestronglyMeasurable).mul hd.aestronglyMeasurable)
  filter_upwards [hupos] with x hx
  have hs : 0 < u x + c := add_pos_of_nonneg_of_pos hx hc
  have hpower : (u x + c) ^ r ≤ 1 + (u x + c) := by
    by_cases hs1 : 1 ≤ u x + c
    · exact (Real.rpow_le_self_of_one_le hs1 hr1).trans (by linarith)
    · exact (Real.rpow_le_one hs.le (le_of_not_ge hs1) hr).trans (by linarith)
  change ‖(u x + c) ^ r * d x‖ ≤ ‖d x‖ + ‖d x * u x‖ + c * ‖d x‖
  rw [norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg hs.le r)]
  have hmul := mul_le_mul_of_nonneg_right hpower (norm_nonneg (d x))
  calc
    _ ≤ (1 + (u x + c)) * ‖d x‖ := hmul
    _ = ‖d x‖ + ‖d x * u x‖ + c * ‖d x‖ := by
      rw [norm_mul, Real.norm_of_nonneg hx]
      ring

/-- A localization equal to one on the cutoff-gradient support supplies the
weighted square integrability from the localized energy-space value. -/
theorem memLp_shifted_small_power_mul_of_plateau {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {u v φ d : α → ℝ} {c r K : ℝ}
    (hc : 0 < c) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hv : MemLp v 2 μ) (hvpos : ∀ᵐ x ∂μ, 0 ≤ v x)
    (hd : MemLp d 2 μ) (hdbound : ∀ᵐ x ∂μ, ‖d x‖ ≤ K)
    (hval : v =ᵐ[μ] fun x => u x * φ x)
    (hplateau : ∀ x, d x ≠ 0 → φ x = 1) :
    MemLp (fun x => (u x + c) ^ r * d x) 2 μ := by
  apply (memLp_congr_ae ?_).mp
    (memLp_shifted_small_power_mul hc hr hr1 hv hvpos hd hdbound)
  filter_upwards [hval] with x hx
  by_cases hdx : d x = 0
  · simp only [hdx, mul_zero]
  · rw [hx, hplateau x hdx, mul_one]

end HeatKernel
