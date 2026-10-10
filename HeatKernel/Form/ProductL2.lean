-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.MeasurableCurves

/-!
# Product square integrability and Bochner L² curves

Tonelli identifies the integral of the spatial L² norm squared with the squared norm on the
product measure. Joint square integrability therefore gives Bochner square integrability of any
curve with the prescribed spatial representatives.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace HeatKernel

/-- Product L² bounds imply Bochner L² bounds for a curve with the same spatial representatives. -/
theorem memLp_L2_of_product_representatives {α β E : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {μ : Measure α} {ν : Measure β} [SFinite ν]
    [SecondCountableTopology (Lp E 2 ν)] {U : α → Lp E 2 ν} {u : α → β → E}
    (hu : MemLp (Function.uncurry u) 2 (μ.prod ν))
    (hrep : ∀ᵐ a ∂μ, U a =ᵐ[ν] u a) : MemLp U 2 μ := by
  have hm := aestronglyMeasurable_L2_of_representatives hu.aestronglyMeasurable hrep
  rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hm]
  simp only [ENNReal.toReal_ofNat]
  have hi : (∫⁻ a, ‖U a‖ₑ ^ (2 : ℝ) ∂μ) =
      ∫⁻ a, ∫⁻ b, ‖u a b‖ₑ ^ (2 : ℝ) ∂ν ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [hrep] with a ha
    rw [Lp.enorm_def, eLpNorm_congr_ae ha]
    have hs := (Lp.aestronglyMeasurable (U a)).congr ha
    exact eLpNorm_nnreal_pow_eq_lintegral (p := 2) (by norm_num) hs
  rw [hi]
  have hton := lintegral_prod _ (hu.aestronglyMeasurable.enorm.pow_const (2 : ℝ))
  simp only [Function.uncurry_def] at hton
  rw [← hton]
  have ht := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hu.eLpNorm_lt_top
  simpa only [ENNReal.toReal_ofNat, Function.uncurry_def] using ht

end HeatKernel
