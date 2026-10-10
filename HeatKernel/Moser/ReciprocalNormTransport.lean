-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueNormalizedScaling

/-! # Reference-mass normalization and transport of reciprocal norms -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace HeatKernel

/-- A reference cylinder can normalize the norm on a smaller source cylinder.
Both reference and source transform by the same Jacobian. -/
theorem eLpNorm_comp_restrict_normalized_by_reference
    {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    (T : E ≃ₜ E) (μ : Measure E) {J : ℝ≥0∞}
    (hm : Measure.map T μ = J • μ) (hJ : J ≠ 0) (hJtop : J ≠ ⊤)
    (f : E → ℝ) (S R : Set E) (p : ℝ≥0∞) :
    eLpNorm (f ∘ T) p ((μ (T ⁻¹' R))⁻¹ • μ.restrict (T ⁻¹' S)) =
      eLpNorm f p ((μ R)⁻¹ • μ.restrict S) := by
  have hmass : μ (T ⁻¹' R) = J * μ R := by
    rw [← T.measurableEmbedding.map_apply, hm, Measure.smul_apply, smul_eq_mul]
  rw [← T.measurableEmbedding.eLpNorm_map_measure,
    Measure.map_smul _ T.measurable.aemeasurable,
    map_restrict_preimage_of_scaled_measure T μ hm S, smul_smul, hmass,
    ENNReal.mul_inv (Or.inl hJ) (Or.inl hJtop)]
  have he : J⁻¹ * (μ R)⁻¹ * J = (μ R)⁻¹ := by
    calc
      _ = (J⁻¹ * J) * (μ R)⁻¹ := by ac_rfl
      _ = _ := by rw [ENNReal.inv_mul_cancel hJ hJtop, one_mul]
  rw [he]

/-- Converting a reciprocal norm estimate to a prescribed finite reference mass
only multiplies its energy constant by that mass. -/
theorem reciprocal_norm_bound_normalized_by_reference
    {E : Type*} [MeasurableSpace E] (μ ν : Measure E) (f : E → ℝ)
    {p L δ κ C : ℝ} {m : ℝ≥0∞} (hp : 0 < p) (hL : 0 ≤ L)
    (hδ : 0 < δ) (hm : m ≠ 0) (hmtop : m ≠ ⊤)
    (hC : L * m.toReal ≤ C)
    (h : eLpNormEssSup f μ ≤
      ENNReal.ofReal ((L / δ ^ κ) ^ (1 / p)) * eLpNorm f (ENNReal.ofReal p) ν) :
    eLpNormEssSup f μ ≤ ENNReal.ofReal ((C / δ ^ κ) ^ (1 / p)) *
      eLpNorm f (ENNReal.ofReal p) (m⁻¹ • ν) := by
  have hfac : 0 ≤ (L / δ ^ κ) ^ (1 / p) := by positivity
  rw [mul_eLpNorm_eq_normalized_eLpNorm ν f hp hfac hm hmtop] at h
  have he : (L / δ ^ κ) ^ (1 / p) * m.toReal ^ (1 / p) =
      (L * m.toReal / δ ^ κ) ^ (1 / p) := by
    rw [← Real.mul_rpow (by positivity) ENNReal.toReal_nonneg]
    congr 1
    ring
  rw [he] at h
  apply h.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal _) le_rfl)
  exact Real.rpow_le_rpow (by positivity)
    (div_le_div_of_nonneg_right hC (Real.rpow_nonneg hδ.le _)) (by positivity)

/-- The normalized reciprocal norm estimate has exactly the moment form used by
Harnack iteration. -/
theorem reciprocal_normalized_norm_bound_to_moment
    {E : Type*} [MeasurableSpace E] (μ : Measure E) (S T : Set E)
    {u : E → ℝ} {c p C δ κ : ℝ} {m : ℝ≥0∞}
    (hu : Measurable u) (hc : 0 < c) (hp : 0 < p) (hC : 0 ≤ C) (hδ : 0 < δ)
    (hu0 : ∀ᵐ z ∂μ.restrict S, 0 ≤ u z)
    (hu0' : ∀ᵐ z ∂μ.restrict T, 0 ≤ u z)
    (h : eLpNormEssSup (fun z => (u z + c)⁻¹) (μ.restrict S) ≤
      ENNReal.ofReal ((C / δ ^ κ) ^ (1 / p)) *
        eLpNorm (fun z => (u z + c)⁻¹) (ENNReal.ofReal p) (m⁻¹ • μ.restrict T)) :
    essSup (fun z => ENNReal.ofReal (1 / (u z + c))) (μ.restrict S) ≤
      (ENNReal.ofReal (C * (1 / δ) ^ κ) * m⁻¹ *
        ∫⁻ z in T, ENNReal.ofReal (1 / (u z + c)) ^ p ∂μ) ^ (1 / p) := by
  have hval : (fun z => ‖(u z + c)⁻¹‖ₑ) =ᵐ[μ.restrict S]
      (fun z => ENNReal.ofReal (1 / (u z + c))) := hu0.mono fun z hz => by
    dsimp only
    rw [one_div, Real.enorm_of_nonneg (inv_nonneg.mpr (add_nonneg hz hc.le))]
  change essSup (fun z => ‖(u z + c)⁻¹‖ₑ) (μ.restrict S) ≤ _ at h
  rw [essSup_congr_ae hval] at h
  have hf : AEStronglyMeasurable (fun z => (u z + c)⁻¹) (m⁻¹ • μ.restrict T) :=
    (hu.add measurable_const).inv.aestronglyMeasurable
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hp).ne'
    ENNReal.ofReal_ne_top hf,
    ENNReal.toReal_ofReal hp.le, lintegral_smul_measure] at h
  have hint : (∫⁻ z in T, ‖(u z + c)⁻¹‖ₑ ^ p ∂μ) =
      ∫⁻ z in T, ENNReal.ofReal (1 / (u z + c)) ^ p ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [hu0'] with z hz
    rw [one_div, Real.enorm_of_nonneg (inv_nonneg.mpr (add_nonneg hz hc.le))]
  rw [hint, ← ENNReal.ofReal_rpow_of_nonneg (by positivity : 0 ≤ C / δ ^ κ)
    (by positivity : 0 ≤ 1 / p), ← ENNReal.mul_rpow_of_nonneg _ _ (by positivity)] at h
  have he : C / δ ^ κ = C * (1 / δ) ^ κ := by
    rw [one_div, Real.inv_rpow hδ.le, div_eq_mul_inv]
  simpa only [he, smul_eq_mul, mul_assoc] using h

end HeatKernel
