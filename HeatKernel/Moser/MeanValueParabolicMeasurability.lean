-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueScaledMeasures
import Mathlib.Tactic

/-! # Measurability and local Lp bounds in parabolic coordinates -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory RothschildStein
open scoped ENNReal
namespace HeatKernel

/-- Parabolic coordinates preserve and reflect all almost everywhere assertions. -/
theorem ae_comp_parabolicGroupHomeomorph_iff {N : ℕ} (G : HomogeneousGroup N)
    (t₀ : ℝ) (x₀ : Fin N → ℝ) (r : ℝ) (hr : 0 < r)
    (P : ℝ × (Fin N → ℝ) → Prop) :
    (∀ᵐ z ∂volume, P (parabolicGroupHomeomorph G t₀ x₀ r hr z)) ↔
      ∀ᵐ z ∂volume, P z :=
  ae_comp_iff_of_scaled_measure (parabolicGroupHomeomorph G t₀ x₀ r hr) volume
    (map_parabolicGroupHomeomorph_volume G t₀ x₀ r hr)
    (ENNReal.ofReal_pos.mpr (inv_pos.mpr (pow_pos hr _))).ne' P

/-- A jointly strongly measurable representative remains strongly measurable on every
subset of the inverse coordinate domain. -/
theorem aestronglyMeasurable_parabolic_pullback {N : ℕ} (G : HomogeneousGroup N)
    (t₀ : ℝ) (x₀ : Fin N → ℝ) (r : ℝ) (hr : 0 < r)
    {f : ℝ × (Fin N → ℝ) → ℝ} {S O : Set (ℝ × (Fin N → ℝ))}
    (hf : AEStronglyMeasurable f (volume.restrict O))
    (hS : S ⊆ (parabolicGroupHomeomorph G t₀ x₀ r hr) ⁻¹' O) :
    AEStronglyMeasurable (f ∘ parabolicGroupHomeomorph G t₀ x₀ r hr)
      (volume.restrict S) :=
  (aestronglyMeasurable_comp_restrict_of_scaled_measure
    (parabolicGroupHomeomorph G t₀ x₀ r hr) volume
    (map_parabolicGroupHomeomorph_volume G t₀ x₀ r hr) hf).mono_measure
      (Measure.restrict_mono hS le_rfl)

/-- Every finite local Lp bound transports to a subset of the inverse coordinate domain. -/
theorem memLp_parabolic_pullback {N : ℕ} (G : HomogeneousGroup N)
    (t₀ : ℝ) (x₀ : Fin N → ℝ) (r : ℝ) (hr : 0 < r)
    {f : ℝ × (Fin N → ℝ) → ℝ} {S O : Set (ℝ × (Fin N → ℝ))} {p : ℝ≥0∞}
    (hf : MemLp f p (volume.restrict O))
    (hS : S ⊆ (parabolicGroupHomeomorph G t₀ x₀ r hr) ⁻¹' O) :
    MemLp (f ∘ parabolicGroupHomeomorph G t₀ x₀ r hr) p (volume.restrict S) :=
  (memLp_comp_restrict_of_scaled_measure (parabolicGroupHomeomorph G t₀ x₀ r hr) volume
    (map_parabolicGroupHomeomorph_volume G t₀ x₀ r hr) ENNReal.ofReal_ne_top hf).mono_measure
      (Measure.restrict_mono hS le_rfl)

end HeatKernel
