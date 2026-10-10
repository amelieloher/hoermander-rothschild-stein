-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueParabolicCoordinates
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Tactic

/-! # Restricted measures and norms under a measure-scaling homeomorphism -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace HeatKernel

variable {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    (T : E ≃ₜ E) (μ : Measure E) {J : ℝ≥0∞}
    (hm : Measure.map T μ = J • μ)

include hm

/-- The same Jacobian applies to restriction to an inverse image. -/
theorem map_restrict_preimage_of_scaled_measure (S : Set E) :
    Measure.map T (μ.restrict (T ⁻¹' S)) = J • μ.restrict S := by
  rw [← T.measurableEmbedding.restrict_map, hm, Measure.restrict_smul]

/-- A nonzero measure scaling preserves and reflects almost everywhere assertions. -/
theorem ae_comp_iff_of_scaled_measure (hJ : J ≠ 0) (P : E → Prop) :
    (∀ᵐ x ∂μ, P (T x)) ↔ ∀ᵐ x ∂μ, P x := by
  rw [← T.measurableEmbedding.ae_map_iff, hm, Measure.ae_ennreal_smul_measure_iff hJ]

/-- Almost everywhere assertions on a restricted domain transport to its inverse image. -/
theorem ae_restrict_comp_iff_of_scaled_measure (hJ : J ≠ 0) (S : Set E) (P : E → Prop) :
    (∀ᵐ x ∂μ.restrict (T ⁻¹' S), P (T x)) ↔ ∀ᵐ x ∂μ.restrict S, P x := by
  rw [← T.measurableEmbedding.ae_map_iff,
    map_restrict_preimage_of_scaled_measure T μ hm S,
    Measure.ae_ennreal_smul_measure_iff hJ]

/-- Strong measurability on a domain transports to its inverse image. -/
theorem aestronglyMeasurable_comp_restrict_of_scaled_measure {f : E → ℝ} {S : Set E}
    (hf : AEStronglyMeasurable f (μ.restrict S)) :
    AEStronglyMeasurable (f ∘ T) (μ.restrict (T ⁻¹' S)) := by
  apply T.measurableEmbedding.aestronglyMeasurable_map_iff.mp
  rw [map_restrict_preimage_of_scaled_measure T μ hm S]
  exact hf.smul_measure J

/-- A finite measure scaling preserves every extended Lp membership on inverse domains. -/
theorem memLp_comp_restrict_of_scaled_measure (hJ : J ≠ ⊤)
    {f : E → ℝ} {S : Set E} {p : ℝ≥0∞} (hf : MemLp f p (μ.restrict S)) :
    MemLp (f ∘ T) p (μ.restrict (T ⁻¹' S)) := by
  apply T.measurableEmbedding.memLp_map_measure_iff.mp
  rw [map_restrict_preimage_of_scaled_measure T μ hm S]
  exact hf.smul_measure hJ

/-- The spatial quadratic norm acquires the square root of the inverse Jacobian. -/
theorem eLpNorm_two_comp_restrict_of_scaled_measure (f : E → ℝ) (S : Set E) :
    eLpNorm (f ∘ T) 2 (μ.restrict (T ⁻¹' S)) =
      J ^ (1 / 2 : ℝ) * eLpNorm f 2 (μ.restrict S) := by
  rw [← T.measurableEmbedding.eLpNorm_map_measure,
    map_restrict_preimage_of_scaled_measure T μ hm S,
    eLpNorm_smul_measure_of_ne_zero_of_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
  norm_num

end HeatKernel
