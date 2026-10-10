-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.ReverseHolderSpacetimeMoments
public import HeatKernel.Moser.MeanValueNestedPowerNorms
public import HeatKernel.Moser.NegativePowerEnergyFactors

/-! Small-positive norm steps with literal outer-cylinder moments. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace HeatKernel

/-- A backward localized moment estimate gives a norm step whose source is the
literal outer-cylinder moment. The local square-integrability hypothesis pays
for the conversion from the real moment to the extended power integral. -/
theorem eLpNorm_small_power_step_le_of_outer_moment {N : ℕ}
    {a b' b c p ν A D : ℝ} (hb'b : b' ≤ b) (hc : 0 < c)
    (hp : 0 < p) (hp1 : p ≤ 1) (hν : 2 < ν) (hA : 1 ≤ A) (hD : 0 ≤ D)
    {V S : Set (Fin N → ℝ)} (hfinite : volume V ≠ ⊤)
    (u : ℝ × (Fin N → ℝ) → ℝ) (hu : Measurable u) (hu0 : ∀ z, 0 ≤ u z)
    (hu2 : MemLp u 2 ((volume.restrict (Icc a b)).prod (volume.restrict V)))
    (θ : ℝ → ℝ) (η : (Fin N → ℝ) → ℝ)
    (hplateau : ∀ᵐ t ∂volume.restrict (Icc a b'),
      ∀ᵐ x ∂volume.restrict S, θ t * η x = 1)
    (hMoment : (∫⁻ t in Icc a b, ∫⁻ x,
      ‖θ t * η x * (u (t, x) + c) ^ (p / 2)‖ₑ ^ (2 + 4 / ν) ∂volume) ≤
        ENNReal.ofReal A * (ENNReal.ofReal D * ENNReal.ofReal
          (∫ t in Icc a b, ∫ x in V, (u (t, x) + c) ^ p)) ^ (1 + 2 / ν)) :
    eLpNorm (fun z => u z + c) (ENNReal.ofReal (p * (1 + 2 / ν)))
      ((volume.restrict (Icc a b')).prod (volume.restrict S)) ≤
        ENNReal.ofReal ((2 * A * D) ^ (1 / p)) *
          eLpNorm (fun z => u z + c) (ENNReal.ofReal p)
            ((volume.restrict (Icc a b)).prod (volume.restrict V)) := by
  have hν0 : 0 < ν := by linarith
  let : IsFiniteMeasure (volume.restrict V) := isFiniteMeasure_restrict.mpr hfinite
  let f := fun z => u z + c
  have hf : Measurable f := hu.add measurable_const
  have hτ : volume.restrict (Icc a b') ≤ volume.restrict (Icc a b) :=
    Measure.restrict_mono (Icc_subset_Icc_right hb'b) le_rfl
  have hcut := lintegral_prod_power_le_cutoff_power_moment hτ
    (Measure.restrict_le_self : (volume : Measure (Fin N → ℝ)).restrict S ≤ volume)
    (fun t x => f (t, x)) (fun t x => θ t * η x) (ν := ν) hp.le
    hf.aestronglyMeasurable hplateau
  have heq : (∫⁻ t in Icc a b, ∫⁻ x,
      ‖‖f (t, x)‖ ^ (p / 2) * (θ t * η x)‖ₑ ^ (2 + 4 / ν) ∂volume) =
      ∫⁻ t in Icc a b, ∫⁻ x,
        ‖θ t * η x * (u (t, x) + c) ^ (p / 2)‖ₑ ^ (2 + 4 / ν) ∂volume := by
    apply lintegral_congr
    intro t
    apply lintegral_congr
    intro x
    dsimp only [f]
    rw [Real.norm_of_nonneg (add_nonneg (hu0 (t, x)) hc.le)]
    congr 2
    ring
  rw [heq] at hcut
  have hsource := (integrable_shifted_small_power_outer_moment
    (volume.restrict (Icc a b)) (volume.restrict V) hc hp.le hp1 hu2
      (Filter.Eventually.of_forall hu0)).2.2
  have hstep := eLpNorm_step_le_of_parabolic_moment_bound _ _ hp
    (show 0 < 1 + 2 / ν by positivity)
    hf.aestronglyMeasurable hf.aestronglyMeasurable
    (hcut.trans (by simpa only [hsource] using hMoment))
  have hχ : 1 ≤ 1 + 2 / ν := le_add_of_nonneg_right (by positivity)
  have hcoef := ennreal_negative_power_energy_iteration_factor_le hA hD hχ hp
  have hDle : ENNReal.ofReal D ≤ 2 * ENNReal.ofReal D :=
    le_mul_of_one_le_left' (by norm_num)
  exact hstep.trans (mul_le_mul' (le_trans
    (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hDle (by positivity))) hcoef) le_rfl)

end HeatKernel
