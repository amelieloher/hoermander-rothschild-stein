-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Semigroup.ProductL2Bounds
public import HeatKernel.Kernel.LocalIntegrability
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-! # Locally integrable joint representatives of bounded L² curves -/

@[expose] public section
noncomputable section
open MeasureTheory Set TopologicalSpace
namespace HeatKernel

theorem exists_locallyIntegrable_joint_L2_representative {n : ℕ}
    (T : ℝ → Lp ℝ 2 (volume : Measure (Fin n → ℝ))) (hT : Continuous T)
    (C : ℝ) (hC : ∀ t, ‖T t‖ ≤ C) :
    ∃ u : ℝ × (Fin n → ℝ) → ℝ, Measurable u ∧
      LocallyIntegrableOn u {z | 0 < z.1} volume ∧
      ∀ t, (fun x => u (t, x)) =ᵐ[volume] T t := by
  let : MeasurableSpace (Lp ℝ 2 (volume : Measure (Fin n → ℝ))) := borel _
  have : BorelSpace (Lp ℝ 2 (volume : Measure (Fin n → ℝ))) := ⟨rfl⟩
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  obtain ⟨u, hu, hslice⟩ := exists_jointly_measurable_L2_representative volume T hT.measurable
  refine ⟨u, hu, ?_, hslice⟩
  apply locallyIntegrableOn_of_memLp_two_on_compacts (isOpen_lt continuous_const continuous_fst)
  intro K _hKpos hK
  obtain ⟨a, ha⟩ := (hK.image continuous_fst).bddBelow
  obtain ⟨b, hb⟩ := (hK.image continuous_fst).bddAbove
  have hstrip : K ⊆ Icc a b ×ˢ (univ : Set (Fin n → ℝ)) := by
    intro z hz
    exact ⟨⟨ha (mem_image_of_mem Prod.fst hz), hb (mem_image_of_mem Prod.fst hz)⟩, mem_univ _⟩
  have hp := memLp_joint_representative_of_bounded_L2_sections
    (volume.restrict (Icc a b)) (volume : Measure (Fin n → ℝ)) T hT.measurable C hC u hu hslice
  rw [Measure.restrict_prod_eq_prod_univ, ← Measure.volume_eq_prod] at hp
  exact MemLp.mono_measure (Measure.restrict_mono hstrip le_rfl) hp

end HeatKernel
