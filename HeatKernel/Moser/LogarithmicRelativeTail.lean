-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic
import all Mathlib.Basic.Real.Basic

/-! # Relative logarithmic tails from a uniform absolute cost -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace HeatKernel

/-- An absolute tail cost bounded by a fixed reference mass gives a relative
tail bound, also when the compact estimation region is smaller than the reference. -/
theorem logarithmic_relative_tail_of_real_cost
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {S V W R : Set α}
    {A B ℓ : ℝ} (hW : MeasurableSet W) (hWfinite : μ W ≠ ⊤)
    (hRfinite : μ R ≠ ⊤) (hVW : V ⊆ W) (hℓ : 0 < ℓ)
    (htail : (μ.restrict W).real S ≤ B / ℓ) (hcost : B ≤ A * μ.real R) :
    μ (V ∩ S) ≤ ENNReal.ofReal (A / ℓ) * μ R := by
  have htailfinite : μ (V ∩ S) ≠ ⊤ :=
    ne_top_of_le_ne_top hWfinite (measure_mono (inter_subset_left.trans hVW))
  have hrfinite : μ.restrict W S ≠ ⊤ := by
    rw [Measure.restrict_apply' hW]
    exact ne_top_of_le_ne_top hWfinite (measure_mono inter_subset_right)
  have hmono : μ (V ∩ S) ≤ μ.restrict W S := by
    rw [Measure.restrict_apply' hW]
    exact measure_mono fun y hy => ⟨hy.2, hVW hy.1⟩
  calc
    μ (V ∩ S) = ENNReal.ofReal (μ.real (V ∩ S)) := (ofReal_measureReal htailfinite).symm
    _ ≤ ENNReal.ofReal (B / ℓ) :=
      ENNReal.ofReal_le_ofReal ((ENNReal.toReal_mono hrfinite hmono).trans htail)
    _ ≤ ENNReal.ofReal ((A / ℓ) * μ.real R) :=
      ENNReal.ofReal_le_ofReal (by
        calc
          B / ℓ ≤ (A * μ.real R) / ℓ := div_le_div_of_nonneg_right hcost hℓ.le
          _ = (A / ℓ) * μ.real R := by ring)
    _ = ENNReal.ofReal (A / ℓ) * μ R := by
      rw [ENNReal.ofReal_mul' measureReal_nonneg, ofReal_measureReal hRfinite]

end HeatKernel
