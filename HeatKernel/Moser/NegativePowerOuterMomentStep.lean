-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.NegativePowerCutoffMoments
public import HeatKernel.Moser.MeanValueNestedPowerNorms
public import HeatKernel.Moser.NegativePowerEnergyFactors

/-! # Reciprocal norm steps with literal outer-cylinder moments -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace HeatKernel

/-- A localized reciprocal moment bounded by the literal outer-cylinder moment
gives the next norm in the iteration. No outer localization cutoff is inserted
in the reciprocal source. -/
theorem eLpNorm_reciprocal_step_le_of_outer_moment {N : ℕ}
    {a a' b c p ν A D : ℝ} (haa' : a ≤ a') (hc : 0 < c)
    (hp : 0 < p) (hν : 2 < ν) (hA : 1 ≤ A) (hD : 0 ≤ D)
    {V S : Set (Fin N → ℝ)} (hfinite : volume V ≠ ⊤)
    (u : ℝ × (Fin N → ℝ) → ℝ) (hu : Measurable u) (hu0 : ∀ z, 0 ≤ u z)
    (θ : ℝ → ℝ) (η : (Fin N → ℝ) → ℝ)
    (hplateau : ∀ᵐ t ∂volume.restrict (Icc a' b),
      ∀ᵐ x ∂volume.restrict S, θ t * η x = 1)
    (hMoment : (∫⁻ t in Icc a b, ∫⁻ x,
      ‖θ t * η x * (u (t, x) + c) ^ (-p / 2)‖ₑ ^ (2 + 4 / ν) ∂volume) ≤
        ENNReal.ofReal A * (ENNReal.ofReal D * ENNReal.ofReal
          (∫ t in Icc a b, ∫ x in V, (u (t, x) + c) ^ (-p))) ^ (1 + 2 / ν)) :
    eLpNorm (fun z => (u z + c)⁻¹) (ENNReal.ofReal (p * (1 + 2 / ν)))
      ((volume.restrict (Icc a' b)).prod (volume.restrict S)) ≤
        ENNReal.ofReal ((2 * A * D) ^ (1 / p)) *
          eLpNorm (fun z => (u z + c)⁻¹) (ENNReal.ofReal p)
            ((volume.restrict (Icc a b)).prod (volume.restrict V)) := by
  have hν0 : 0 < ν := by linarith
  let : IsFiniteMeasure (volume.restrict V) := isFiniteMeasure_restrict.mpr hfinite
  let f := fun z => (u z + c)⁻¹
  have hf : Measurable f := (hu.add measurable_const).inv
  have hτ : volume.restrict (Icc a' b) ≤ volume.restrict (Icc a b) :=
    Measure.restrict_mono (Icc_subset_Icc_left haa') le_rfl
  have hcut := lintegral_prod_power_le_cutoff_power_moment hτ
    (Measure.restrict_le_self : (volume : Measure (Fin N → ℝ)).restrict S ≤ volume)
    (fun t x => f (t, x)) (fun t x => θ t * η x) (ν := ν) hp.le
    hf.aestronglyMeasurable hplateau
  have heq : (∫⁻ t in Icc a b, ∫⁻ x,
      ‖‖f (t, x)‖ ^ (p / 2) * (θ t * η x)‖ₑ ^ (2 + 4 / ν) ∂volume) =
      ∫⁻ t in Icc a b, ∫⁻ x,
        ‖θ t * η x * (u (t, x) + c) ^ (-p / 2)‖ₑ ^ (2 + 4 / ν) ∂volume := by
    apply lintegral_congr
    intro t
    apply lintegral_congr
    intro x
    dsimp only [f]
    rw [Real.norm_of_nonneg (inv_nonneg.mpr (add_nonneg (hu0 (t, x)) hc.le)),
      ← Real.rpow_neg_eq_inv_rpow]
    congr 2
    rw [neg_div]
    ring
  rw [heq] at hcut
  have hm := integrableOn_reciprocal_spatial_moment (a := a) (b := b) hfinite hu hu0 hc hp
  have hsource : ENNReal.ofReal (∫ t in Icc a b, ∫ x in V, (u (t, x) + c) ^ (-p)) =
      ∫⁻ z, ‖f z‖ₑ ^ p ∂(volume.restrict (Icc a b)).prod (volume.restrict V) := by
    rw [ofReal_integral_eq_lintegral_ofReal hm
      (Filter.Eventually.of_forall fun t => integral_nonneg fun x =>
        Real.rpow_nonneg (add_nonneg (hu0 (t, x)) hc.le) _),
      lintegral_prod _ (hf.aemeasurable.enorm.pow_const p)]
    apply lintegral_congr
    intro t
    exact ofReal_integral_reciprocal_power_eq_lintegral
      ((hu.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => hu0 (t, x)) hc hp
  have hstep := eLpNorm_step_le_of_parabolic_moment_bound _ _ hp
    (show 0 < 1 + 2 / ν by positivity)
    hf.aestronglyMeasurable hf.aestronglyMeasurable
    (hcut.trans (by simpa only [hsource] using hMoment))
  have hχ : 1 ≤ 1 + 2 / ν := le_add_of_nonneg_right
    (by positivity)
  have hcoef := ennreal_negative_power_energy_iteration_factor_le hA hD hχ hp
  have hDle : ENNReal.ofReal D ≤ 2 * ENNReal.ofReal D := by
    exact le_mul_of_one_le_left' (by norm_num)
  exact hstep.trans (mul_le_mul' (le_trans
    (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hDle (by positivity))) hcoef) le_rfl)

end HeatKernel
