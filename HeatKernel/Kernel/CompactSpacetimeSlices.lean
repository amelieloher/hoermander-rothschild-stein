-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.L2TimeTests
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Spatial slices of compact spacetime tests

The projections of a compact spacetime support simultaneously control
all spatial supports and the time support of the corresponding L² curve.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace HeatKernel

/-- Every spatial slice is supported in the spatial projection of the spacetime support. -/
theorem tsupport_spatial_slice_subset_projection {n : ℕ}
    (φ : ℝ × (Fin n → ℝ) → ℝ) (hc : HasCompactSupport φ) (t : ℝ) :
    tsupport (fun x => φ (t, x)) ⊆ Prod.snd '' tsupport φ := by
  apply closure_minimal _ (hc.image continuous_snd).isClosed
  intro x hx
  by_contra hnot
  have hz : (t, x) ∉ tsupport φ := fun h => hnot ⟨(t, x), h, rfl⟩
  exact hx (image_eq_zero_of_notMem_tsupport hz)

/-- Compact spacetime support gives compact support of every spatial slice. -/
theorem hasCompactSupport_spatial_slice {n : ℕ}
    (φ : ℝ × (Fin n → ℝ) → ℝ) (hc : HasCompactSupport φ) (t : ℝ) :
    HasCompactSupport (fun x => φ (t, x)) :=
  (hc.image continuous_snd).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_spatial_slice_subset_projection φ hc t)

/-- Continuous compact spacetime tests have L² spatial slices. -/
theorem memLp_two_spatial_slice {n : ℕ}
    (φ : ℝ × (Fin n → ℝ) → ℝ) (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (t : ℝ) : MemLp (fun x => φ (t, x)) 2 volume :=
  (hφ.comp (continuous_const.prodMk continuous_id)).memLp_of_hasCompactSupport
    (hasCompactSupport_spatial_slice φ hc t)

/-- Spatial slices vanish outside the time projection of the spacetime support. -/
theorem spatial_slice_eq_zero_outside_time_projection {n : ℕ}
    (φ : ℝ × (Fin n → ℝ) → ℝ) {t : ℝ}
    (ht : t ∉ Prod.fst '' tsupport φ) : (fun x => φ (t, x)) = 0 := by
  funext x
  exact image_eq_zero_of_notMem_tsupport (fun h => ht ⟨(t, x), h, rfl⟩)

end HeatKernel
