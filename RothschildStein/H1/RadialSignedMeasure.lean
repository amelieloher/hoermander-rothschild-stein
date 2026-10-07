-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace RothschildStein.H1

/-- An integrable signed density annihilating every interval of a
measurable radial map has equal positive and negative pushforwards. -/
theorem map_positiveDensity_eq_map_negativeDensity
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f ν : α → ℝ} (hf : Integrable f μ) (hν : Measurable ν)
    (he : ∀ a b : ℝ, ∫ x in ν ⁻¹' Icc a b, f x ∂μ = 0) :
    (μ.withDensity (fun x => ENNReal.ofReal (f x))).map ν =
      (μ.withDensity (fun x => ENNReal.ofReal (-f x))).map ν := by
  have hp : ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≠ ∞ := by
    apply ne_of_lt
    exact lt_of_le_of_lt (lintegral_mono fun x => Real.ofReal_le_enorm (f x))
      hf.hasFiniteIntegral
  have hn : ∫⁻ x, ENNReal.ofReal (-f x) ∂μ ≠ ∞ := by
    apply ne_of_lt
    exact lt_of_le_of_lt (lintegral_mono fun x => by simpa only [enorm_neg] using Real.ofReal_le_enorm (-f x))
      hf.hasFiniteIntegral
  have : IsFiniteMeasure (μ.withDensity (fun x => ENNReal.ofReal (f x))) :=
    isFiniteMeasure_withDensity hp
  have : IsFiniteMeasure (μ.withDensity (fun x => ENNReal.ofReal (-f x))) :=
    isFiniteMeasure_withDensity hn
  apply Measure.ext_of_Icc
  intro a b _
  rw [Measure.map_apply hν measurableSet_Icc, Measure.map_apply hν measurableSet_Icc,
    withDensity_apply _ (hν measurableSet_Icc),
    withDensity_apply _ (hν measurableSet_Icc)]
  have hps : ∫⁻ x in ν ⁻¹' Icc a b, ENNReal.ofReal (f x) ∂μ ≠ ∞ :=
    ne_of_lt (lt_of_le_of_lt (lintegral_mono' Measure.restrict_le_self le_rfl) (lt_top_iff_ne_top.mpr hp))
  have hns : ∫⁻ x in ν ⁻¹' Icc a b, ENNReal.ofReal (-f x) ∂μ ≠ ∞ :=
    ne_of_lt (lt_of_le_of_lt (lintegral_mono' Measure.restrict_le_self le_rfl) (lt_top_iff_ne_top.mpr hn))
  apply (ENNReal.toReal_eq_toReal_iff' hps hns).mp
  have hi : IntegrableOn f (ν ⁻¹' Icc a b) μ := hf.integrableOn
  have h := integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi
  rw [he a b] at h
  linarith

end RothschildStein.H1
