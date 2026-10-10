-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueNormScaling
import Mathlib.Tactic

/-! # Invariance of normalized means under parabolic coordinates -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set MeasureTheory RothschildStein
open scoped ENNReal
namespace HeatKernel

/-- A finite positive reference mass converts an unnormalized power norm into
the corresponding normalized norm, including infinite function norms. -/
theorem mul_eLpNorm_eq_normalized_eLpNorm
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ)
    {p A : ℝ} {m : ℝ≥0∞} (hp : 0 < p) (hA : 0 ≤ A)
    (hm : m ≠ 0) (hmtop : m ≠ ⊤) :
    ENNReal.ofReal A * eLpNorm f (ENNReal.ofReal p) μ =
      ENNReal.ofReal (A * m.toReal ^ (1 / p)) *
        eLpNorm f (ENNReal.ofReal p) (m⁻¹ • μ) := by
  have hmpos : 0 < m.toReal := ENNReal.toReal_pos hm hmtop
  have hcancel : m ^ (1 / p) * m⁻¹ ^ (1 / p) = 1 := by
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
      ENNReal.mul_inv_cancel hm hmtop, ENNReal.one_rpow]
  rw [ENNReal.ofReal_mul hA, ← ENNReal.ofReal_rpow_of_pos hmpos,
    ENNReal.ofReal_toReal hmtop, eLpNorm_smul_measure_of_ne_zero_of_ne_top
      (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofReal hp.le, one_div, smul_eq_mul]
  have h := congrArg (fun z : ℝ≥0∞ => ENNReal.ofReal A * z * eLpNorm f (ENNReal.ofReal p) μ)
    hcancel
  simpa only [mul_one, mul_assoc, one_div] using h.symm

/-- Normalizing restricted measures cancels a finite nonzero constant Jacobian. -/
theorem map_normalized_restrict_of_scaled_measure
    {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    (T : E ≃ₜ E) (μ : Measure E) {J : ℝ≥0∞}
    (hm : Measure.map T μ = J • μ) (hJ : J ≠ 0) (hJtop : J ≠ ⊤) (S : Set E) :
    Measure.map T ((μ (T ⁻¹' S))⁻¹ • μ.restrict (T ⁻¹' S)) =
      (μ S)⁻¹ • μ.restrict S := by
  have hmass : μ (T ⁻¹' S) = J * μ S := by
    rw [← T.measurableEmbedding.map_apply, hm, Measure.smul_apply, smul_eq_mul]
  rw [Measure.map_smul _ T.measurable.aemeasurable,
    map_restrict_preimage_of_scaled_measure T μ hm S, smul_smul, hmass,
    ENNReal.mul_inv (Or.inl hJ) (Or.inl hJtop)]
  congr 1
  calc
    J⁻¹ * (μ S)⁻¹ * J = (J⁻¹ * J) * (μ S)⁻¹ := by ac_rfl
    _ = (μ S)⁻¹ := by rw [ENNReal.inv_mul_cancel hJ hJtop, one_mul]

/-- Every extended power norm is unchanged when both domains carry their normalized
restricted measures. No finiteness or measurability hypothesis on the function is needed. -/
theorem eLpNorm_normalized_comp_restrict_of_scaled_measure
    {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    (T : E ≃ₜ E) (μ : Measure E) {J : ℝ≥0∞}
    (hm : Measure.map T μ = J • μ) (hJ : J ≠ 0) (hJtop : J ≠ ⊤)
    (f : E → ℝ) (S : Set E) (p : ℝ≥0∞) :
    eLpNorm (f ∘ T) p ((μ (T ⁻¹' S))⁻¹ • μ.restrict (T ⁻¹' S)) =
      eLpNorm f p ((μ S)⁻¹ • μ.restrict S) := by
  rw [← T.measurableEmbedding.eLpNorm_map_measure,
    map_normalized_restrict_of_scaled_measure T μ hm hJ hJtop S]

end HeatKernel
