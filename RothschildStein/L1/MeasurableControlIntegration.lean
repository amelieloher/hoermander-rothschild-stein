-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.ScalarIntegration
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators

namespace RothschildStein.L1

/-- Bounded measurable controls times continuous coefficients
are integrable on the full compact time interval. -/
theorem intervalIntegrable_control_sum {q : ℕ} {a b : ℝ}
    (c p : Fin q → ℝ → ℝ) (C : Fin q → ℝ)
    (hc : ∀ i, AEMeasurable (c i) (volume.restrict (uIcc a b)))
    (hbound : ∀ i, ∀ᵐ t ∂volume.restrict (uIcc a b), |c i t| ≤ C i)
    (hp : ∀ i, ContinuousOn (p i) (uIcc a b)) :
    IntervalIntegrable (fun t => ∑ i, c i t * p i t) volume a b := by
  apply (intervalIntegrable_iff').mpr
  apply integrable_finsetSum
  intro i _
  exact ((hp i).integrableOn_compact isCompact_uIcc).bdd_mul
    (hc i).aestronglyMeasurable (by simpa only [Real.norm_eq_abs] using hbound i)

end RothschildStein.L1
