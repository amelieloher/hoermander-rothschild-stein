-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.TopExhaustionBounds
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Tactic

/-! # Essential bounds from uniform terminal-time estimates -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace HeatKernel
set_option backward.isDefEq.respectTransparency false

/-- Uniform terminal bounds pass to the open top time even if they are available
only for terminal times beyond a fixed strictly interior threshold. -/
theorem eLpNormEssSup_prod_Ioo_le_of_uniform_terminal_bounds
    {α : Type*} [MeasurableSpace α] (μ : Measure (ℝ × α)) (f : ℝ × α → ℝ)
    {a c T : ℝ} (hc : c < T) (B : Set α) (K : ℝ≥0∞)
    (hbound : ∀ b : ℝ, c ≤ b → b < T →
      eLpNormEssSup f (μ.restrict (Ioo a b ×ˢ B)) ≤ K) :
    eLpNormEssSup f (μ.restrict (Ioo a T ×ˢ B)) ≤ K := by
  change essSup (fun z => ‖f z‖ₑ) (μ.restrict (Ioo a T ×ˢ B)) ≤ K
  apply essSup_prod_Ioo_le_of_interiorTopTime_bounds μ a T B (fun z => ‖f z‖ₑ)
  intro n
  let b := max c (interiorTopTime T n)
  have hb := hbound b (le_max_left _ _) (max_lt hc (interiorTopTime_lt T n))
  have hsub : Ioo a (interiorTopTime T n) ×ˢ B ⊆ Ioo a b ×ˢ B :=
    Set.prod_mono (Ioo_subset_Ioo le_rfl (le_max_right _ _)) Subset.rfl
  exact (eLpNormEssSup_mono_measure f
    (Measure.absolutelyContinuous_of_le (Measure.restrict_mono hsub le_rfl))).trans hb

end HeatKernel
