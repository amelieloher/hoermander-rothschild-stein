-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.TopExhaustionBounds
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.Order.Basic

/-! # Cylinder estimates from almost every terminal time -/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace HeatKernel

/-- Good terminal times can be selected above every interior cutoff. -/
theorem exists_good_terminal_time_of_ae {a b t : ℝ} (hab : a < b) (ht : t < b)
    {P : ℝ → Prop} (hP : ∀ᵐ s ∂volume.restrict (Ioo a b), P s) :
    ∃ s, a < s ∧ t < s ∧ s < b ∧ P s := by
  have hd : Dense {s | s ∈ Ioo a b → P s} :=
    (volume : Measure ℝ).dense_of_ae ((ae_restrict_iff' measurableSet_Ioo).mp hP)
  obtain ⟨s, hs, hms, hsb⟩ := hd.exists_between (max_lt hab ht)
  have has : a < s := (le_max_left a t).trans_lt hms
  exact ⟨s, has, (le_max_right a t).trans_lt hms, hsb, hs ⟨has, hsb⟩⟩

end HeatKernel
