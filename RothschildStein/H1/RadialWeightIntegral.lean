-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.RadialSignedMeasure

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.H1

/-- Equality of radial signed masses yields cancellation after any
bounded measurable radial weighting. -/
theorem integral_radialWeight_zero
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f ν : α → ℝ} (hf : Integrable f μ) (hν : Measurable ν)
    (he : ∀ a b : ℝ, ∫ x in ν ⁻¹' Icc a b, f x ∂μ = 0)
    {Φ : ℝ → ℝ} (hΦ : Measurable Φ) {C : ℝ} (hb : ∀ t, ‖Φ t‖ ≤ C) :
    ∫ x, f x * Φ (ν x) ∂μ = 0 := by
  have hm := map_positiveDensity_eq_map_negativeDensity hf hν he
  have hiP : Integrable (fun x => max (f x) 0 * Φ (ν x)) μ :=
    hf.pos_part.mul_bdd (hΦ.comp hν).aestronglyMeasurable (Filter.Eventually.of_forall fun x => hb (ν x))
  have hiN : Integrable (fun x => max (-f x) 0 * Φ (ν x)) μ :=
    hf.neg_part.mul_bdd (hΦ.comp hν).aestronglyMeasurable (Filter.Eventually.of_forall fun x => hb (ν x))
  have hfneg : Integrable (fun x => -f x) μ := by simpa using hf.neg
  have hEq : (∫ x, max (f x) 0 * Φ (ν x) ∂μ) =
      ∫ x, max (-f x) 0 * Φ (ν x) ∂μ := by
    have h := congrArg (fun m : Measure ℝ => ∫ t, Φ t ∂m) hm
    rw [integral_map_of_stronglyMeasurable hν hΦ.stronglyMeasurable,
      integral_map_of_stronglyMeasurable hν hΦ.stronglyMeasurable,
      integral_withDensity_eq_integral_toReal_smul₀ hf.aestronglyMeasurable.aemeasurable.ennreal_ofReal
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
      integral_withDensity_eq_integral_toReal_smul₀ hfneg.aestronglyMeasurable.aemeasurable.ennreal_ofReal
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at h
    simpa only [ENNReal.toReal_ofReal', smul_eq_mul] using h
  have hpoint : (fun x => f x * Φ (ν x)) =
      fun x => max (f x) 0 * Φ (ν x) - max (-f x) 0 * Φ (ν x) := by
    funext x
    by_cases hx : 0 ≤ f x
    · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx), zero_mul, sub_zero]
    · rw [max_eq_right (le_of_not_ge hx), max_eq_left (neg_nonneg.mpr (le_of_not_ge hx)),
        zero_mul, neg_mul, zero_sub, neg_neg]
  rw [hpoint, integral_sub hiP hiN, hEq, sub_self]

end RothschildStein.H1
