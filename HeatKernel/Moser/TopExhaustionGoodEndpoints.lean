-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.WeakSolutionCutoffDualEquation
public import HeatKernel.Moser.WeakSolutionEnergyIdentityLimits
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.Order.IsLUB

/-! # Increasing good terminal times for nonlinear energy exhaustion -/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter TopologicalSpace
open scoped Topology
namespace HeatKernel

/-- A property holding almost everywhere on an open interval holds along an increasing
sequence tending to its top. -/
theorem exists_strictMono_good_terminal_times {a b : ℝ} (hab : a < b)
    {P : ℝ → Prop} (hP : ∀ᵐ t ∂volume.restrict (Ioo a b), P t) :
    ∃ s : ℕ → ℝ, StrictMono s ∧ (∀ n, a < s n ∧ s n < b ∧ P (s n)) ∧
      Tendsto s atTop (𝓝 b) := by
  have hd : Dense {t | t ∈ Ioo a b → P t} :=
    (volume : Measure ℝ).dense_of_ae ((ae_restrict_iff' measurableSet_Ioo).mp hP)
  obtain ⟨s, hs, hm, ht⟩ := hd.exists_seq_strictMono_tendsto_of_lt hab
  exact ⟨s, hs, fun n => ⟨(hm n).1.1, (hm n).1.2, (hm n).2 (hm n).1⟩, ht⟩

end HeatKernel
