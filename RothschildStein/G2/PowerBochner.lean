-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.MeasureConsequences

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.G2
variable {N : ℕ} {G : HomogeneousGroup N}

private theorem power_measurable {ν : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (β : ℝ) : Measurable (fun x => (ν x) ^ (-β)) := hν.1.measurable.pow_const _

private theorem power_nonneg {ν : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (β : ℝ) : ∀ x, 0 ≤ (ν x) ^ (-β) := fun x => Real.rpow_nonneg (hν.2.1 x) _

/-- The power function is Lebesgue integrable on a closed gauge
sublevel exactly when β < Q (BB Prop 3.21, pp. 105–106). -/
theorem integrableOn_power_near_iff {ν : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (β : ℝ) {R : ℝ} (hR : 0 < R) :
    IntegrableOn (fun x => (ν x) ^ (-β)) {x | ν x ≤ R} ↔ β < G.homogeneousDimension :=
  (lintegral_ofReal_ne_top_iff_integrable (power_measurable hν β).aestronglyMeasurable
    (Filter.Eventually.of_forall (power_nonneg hν β))).symm.trans
    (power_lintegral_near_finite_iff hν β hR)

/-- The exact real-valued near-zero power integral Qm R^(Q−β)/(Q−β)
(BB Proposition 3.21, pp. 105–106; the exponent depends on the homogeneous dimension). -/
theorem integral_power_near {ν : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    {β R : ℝ} (hβ : β < G.homogeneousDimension) (hR : 0 < R) :
    (∫ x in {x | ν x ≤ R}, (ν x) ^ (-β)) =
      (G.homogeneousDimension : ℝ) * (volume {x | ν x < 1}).toReal *
        R ^ ((G.homogeneousDimension : ℝ) - β) / ((G.homogeneousDimension : ℝ) - β) := by
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (power_nonneg hν β))
    (power_measurable hν β).aestronglyMeasurable, power_lintegral_near hν hβ hR]
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Nat.cast_nonneg _), ENNReal.toReal_ofReal
      (div_nonneg (Real.rpow_nonneg hR.le _) (by linarith))]
  ring

end RothschildStein.G2
