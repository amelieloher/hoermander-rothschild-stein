-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib
public import HeatKernel.Form.SteklovRepresentatives

/-!
# Differentiation of one-sided time averages

For a continuous Banach-valued curve, the derivative of its time average is
the corresponding difference quotient. Continuous linear functionals commute
with the averages. Locally integrable curves satisfy the same derivative
formulas almost everywhere by Lebesgue differentiation.
-/

@[expose] public section

open MeasureTheory

namespace HeatKernel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Forward averages of locally integrable curves have the difference-quotient derivative
almost everywhere. -/
theorem ae_hasDerivAt_forwardTimeAverage {u : ℝ → E}
    (hu : LocallyIntegrable u volume) (h : ℝ) :
    ∀ᵐ t ∂volume, HasDerivAt (forwardTimeAverage h u)
      (h⁻¹ • (u (t + h) - u t)) t := by
  have hi (a b : ℝ) : IntervalIntegrable u volume a b :=
    (hu.integrableOn_isCompact isCompact_uIcc).intervalIntegrable
  have he : forwardTimeAverage h u =
      (fun t => h⁻¹ • ((∫ s in (0 : ℝ)..t + h, u s) - ∫ s in (0 : ℝ)..t, u s)) := by
    funext t
    dsimp [forwardTimeAverage]
    congr 1
    exact eq_sub_of_add_eq' (intervalIntegral.integral_add_adjacent_intervals
      (hi 0 t) (hi t (t + h)))
  have hd := LocallyIntegrable.ae_hasDerivAt_integral hu
  have hs := (measurePreserving_add_right volume h).quasiMeasurePreserving.ae hd
  filter_upwards [hd, hs] with t ht hth
  rw [he]
  have hr := (hth 0).scomp t ((hasDerivAt_id t).add_const h)
  simpa [Function.comp_def, Pi.smul_def, Pi.sub_def] using (hr.sub (ht 0)).const_smul h⁻¹

/-- The derivative of a backward time average is its backward difference quotient. -/
theorem hasDerivAt_backwardTimeAverage_of_continuous {u : ℝ → E} (hu : Continuous u)
    (h t : ℝ) : HasDerivAt (backwardTimeAverage h u)
      (h⁻¹ • (u t - u (t - h))) t := by
  have he : backwardTimeAverage h u =
      (fun t => h⁻¹ • ((∫ s in (0 : ℝ)..t, u s) - ∫ s in (0 : ℝ)..t - h, u s)) := by
    funext t
    dsimp [backwardTimeAverage]
    congr 1
    have hi := intervalIntegral.integral_add_adjacent_intervals
      (hu.intervalIntegrable (μ := volume) 0 (t - h)) (hu.intervalIntegrable (μ := volume) (t - h) t)
    exact eq_sub_of_add_eq' hi
  rw [he]
  have hl := (hu.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hr := ((hu.integral_hasStrictDerivAt 0 (t - h)).hasDerivAt).scomp t
    ((hasDerivAt_id t).sub_const h)
  simpa [Function.comp_def, Pi.smul_def, Pi.sub_def] using (hl.sub hr).const_smul h⁻¹

end HeatKernel
