-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.TopExhaustionAlmostEverywhere
public import Mathlib.MeasureTheory.Measure.Continuity

/-! # Tail measures and essential bounds up to an open terminal time -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace HeatKernel

/-- Uniform tail-measure bounds pass to the open top endpoint. Neither the tail
set nor the spatial region needs a separate measurability hypothesis. -/
theorem measure_inter_prod_Ioo_le_of_interiorTopTime_bounds
    {E : Type*} [MeasurableSpace E] (μ : Measure (ℝ × E))
    (a b : ℝ) (B S : Set (ℝ × E)) {C : ℝ≥0∞}
    (hbound : ∀ n, μ (S ∩ B ∩ (Ioo a (interiorTopTime b n) ×ˢ univ)) ≤ C) :
    μ (S ∩ B ∩ (Ioo a b ×ˢ univ)) ≤ C := by
  have hm : Monotone (fun n : ℕ => S ∩ B ∩ (Ioo a (interiorTopTime b n) ×ˢ univ)) := by
    intro m n hmn z hz
    exact ⟨hz.1, ⟨⟨hz.2.1.1,
      hz.2.1.2.trans_le (monotone_interiorTopTime b hmn)⟩, hz.2.2⟩⟩
  have hu : (⋃ n : ℕ, S ∩ B ∩ (Ioo a (interiorTopTime b n) ×ˢ univ)) =
      S ∩ B ∩ (Ioo a b ×ˢ univ) := by
    rw [← inter_iUnion, iUnion_prod_Ioo_interiorTopTime]
  rw [← hu, hm.measure_iUnion]
  exact iSup_le hbound

/-- Uniform essential bounds at almost every terminal time in any cofinal
interior window control the full open-top cylinder. -/
theorem essSup_prod_Ioo_le_of_ae_cofinal_terminal_bounds
    {E : Type*} [MeasurableSpace E] (μ : Measure (ℝ × E))
    {a c b : ℝ} (hcb : c < b) (B : Set E) (f : ℝ × E → ℝ≥0∞) {C : ℝ≥0∞}
    (hbound : ∀ᵐ s ∂volume.restrict (Ioo c b),
      essSup f (μ.restrict (Ioo a s ×ˢ B)) ≤ C) :
    essSup f (μ.restrict (Ioo a b ×ˢ B)) ≤ C := by
  apply essSup_prod_Ioo_le_of_interiorTopTime_bounds μ a b B f
  intro n
  obtain ⟨s, _, hns, _, hs⟩ :=
    exists_good_terminal_time_of_ae hcb (interiorTopTime_lt b n) hbound
  apply (essSup_mono_measure' (Measure.restrict_mono ?_ le_rfl)).trans hs
  intro z hz
  exact ⟨⟨hz.1.1, hz.1.2.trans hns⟩, hz.2⟩

end HeatKernel
