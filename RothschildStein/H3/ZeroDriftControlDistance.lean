-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Definitions.controlDistance
public import RothschildStein.Definitions.noDriftWeight
public import RothschildStein.Definitions.driftWeight
public import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal BigOperators
namespace RothschildStein.H3

/-- Adding a zero drift channel preserves
the exact controlled curves and their cost: its coefficient may be
removed, and the reverse transport sets that coefficient to zero. -/
theorem isControlledCurve_zero_drift_iff {N q : ℕ}
    (Ω : Set (Fin N → ℝ)) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (δ : ℝ) (γ : ℝ → (Fin N → ℝ)) :
    isControlledCurve Ω driftWeight (Fin.cases 0 X) δ γ ↔
      isControlledCurve Ω noDriftWeight X δ γ := by
  constructor
  · rintro ⟨hd, hc, hm, a, ham, hae⟩
    refine ⟨hd, hc, hm, fun i => a i.succ, fun i => ham i.succ, ?_⟩
    filter_upwards [hae] with t ht
    refine ⟨fun i => ?_, ?_⟩
    · simpa [driftWeight, noDriftWeight] using ht.1 i.succ
    · simpa only [Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ,
        Pi.zero_apply, smul_zero, zero_add] using ht.2
  · rintro ⟨hd, hc, hm, a, ham, hae⟩
    let b : Fin (q + 1) → ℝ → ℝ := Fin.cases (fun _ => 0) a
    refine ⟨hd, hc, hm, b, ?_, ?_⟩
    · intro i
      cases i using Fin.cases with
      | zero => exact aemeasurable_const
      | succ i => exact ham i
    · filter_upwards [hae] with t ht
      refine ⟨?_, ?_⟩
      · intro i
        cases i using Fin.cases with
        | zero => simpa [b, driftWeight] using sq_nonneg δ
        | succ i => simpa [b, driftWeight, noDriftWeight] using ht.1 i
      · simpa only [b, Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ,
          Pi.zero_apply, smul_zero, zero_add] using ht.2

/-- The literal fixed control distances
agree pointwise after adding a zero drift channel. -/
theorem controlDistance_zero_drift_eq {N q : ℕ}
    (Ω : Set (Fin N → ℝ)) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (x y : Fin N → ℝ) :
    controlDistance Ω driftWeight (Fin.cases 0 X) x y =
      controlDistance Ω noDriftWeight X x y := by
  unfold controlDistance
  simp_rw [isControlledCurve_zero_drift_iff]

end RothschildStein.H3
