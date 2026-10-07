-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.PowerReduction

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace RothschildStein.G2

private theorem rpow_near_finite (p : ℝ) {R : ℝ} (hR : 0 < R) :
    (∫⁻ r in Ioc (0 : ℝ) R, ENNReal.ofReal (r ^ p)) ≠ ⊤ ↔ -1 < p := by
  rw [← restrict_Ioo_eq_restrict_Ioc]
  rw [lintegral_ofReal_ne_top_iff_integrable (by fun_prop)]
  · exact intervalIntegral.integrableOn_Ioo_rpow_iff hR
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact Real.rpow_nonneg hr.1.le p

private theorem rpow_near_value {p R : ℝ} (hp : -1 < p) (hR : 0 < R) :
    (∫⁻ r in Ioc (0 : ℝ) R, ENNReal.ofReal (r ^ p)) = ENNReal.ofReal (R ^ (p + 1) / (p + 1)) := by
  have hf : IntegrableOn (fun r : ℝ => r ^ p) (Ioc 0 R) := by
    unfold IntegrableOn
    rw [← restrict_Ioo_eq_restrict_Ioc]
    exact (intervalIntegral.integrableOn_Ioo_rpow_iff hR).mpr hp
  rw [← ofReal_integral_eq_lintegral_ofReal hf]
  · rw [← intervalIntegral.integral_of_le hR.le,
      integral_rpow (Or.inl hp)]
    simp [Real.zero_rpow (by linarith : p + 1 ≠ 0)]
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact Real.rpow_nonneg hr.1.le p

private theorem radial_coefficient_good {N : ℕ} {G : HomogeneousGroup N}
    {ν : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν) :
    ENNReal.ofReal (G.homogeneousDimension : ℝ) * volume {x | ν x < 1} ≠ 0 ∧
    ENNReal.ofReal (G.homogeneousDimension : ℝ) * volume {x | ν x < 1} ≠ ⊤ := by
  have hQ : 0 < G.homogeneousDimension := by
    unfold HomogeneousGroup.homogeneousDimension
    exact Finset.sum_pos (fun j _ => G.weight_pos j)
      (Finset.univ_nonempty_iff.mpr ⟨⟨0, G.dimension_pos⟩⟩)
  have hm : 0 < volume {x | ν x < 1} :=
    (hν.1.isOpen_preimage _ isOpen_Iio).measure_pos volume
      ⟨0, by change ν 0 < 1; rw [(hν.2.2.1 0).mpr rfl]; exact zero_lt_one⟩
  have hmf : volume {x | ν x < 1} ≠ ⊤ :=
    ne_top_of_le_ne_top ((isCompact_gauge_le hν 1).measure_ne_top (μ := volume))
      (measure_mono fun x (hx : ν x < 1) => hx.le)
  exact ⟨mul_ne_zero (ne_of_gt (ENNReal.ofReal_pos.mpr (Nat.cast_pos.mpr hQ))) hm.ne',
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmf⟩

/-- Integrability near zero holds exactly for β < Q; equality is excluded by dilation-volume scaling (BB Proposition 3.21, pp. 105–106). -/
theorem power_lintegral_near_finite_iff_of_volumeScaling {N : ℕ} {G : HomogeneousGroup N}
    (hscale : ∀ r : ℝ, 0 < r → ∀ A : Set (Fin N → ℝ),
      volume ((G.dilate r) '' A) = ENNReal.ofReal (r ^ G.homogeneousDimension) * volume A)
    {ν : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν) (β : ℝ) {R : ℝ} (hR : 0 < R) :
    (∫⁻ x in {x | ν x ≤ R}, ENNReal.ofReal ((ν x) ^ (-β))) ≠ ⊤ ↔ β < G.homogeneousDimension := by
  rw [power_lintegral_near_reduction_of_volumeScaling hscale hν β R]
  obtain ⟨hc0, hcf⟩ := radial_coefficient_good hν
  simp only [ne_eq, ENNReal.mul_eq_top, hcf, hc0, not_false_eq_true, false_and, true_and, or_false]
  exact (rpow_near_finite ((G.homogeneousDimension : ℝ) - 1 - β) hR).trans
    (by constructor <;> intro h <;> linarith)

/-- The exact near-zero power integral has constant Qm/(Q−β), by dilation-volume scaling (BB Proposition 3.21, pp. 105–106). -/
theorem power_lintegral_near_of_volumeScaling {N : ℕ} {G : HomogeneousGroup N}
    (hscale : ∀ r : ℝ, 0 < r → ∀ A : Set (Fin N → ℝ),
      volume ((G.dilate r) '' A) = ENNReal.ofReal (r ^ G.homogeneousDimension) * volume A)
    {ν : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν) {β R : ℝ}
    (hβ : β < G.homogeneousDimension) (hR : 0 < R) :
    (∫⁻ x in {x | ν x ≤ R}, ENNReal.ofReal ((ν x) ^ (-β))) =
      ENNReal.ofReal (G.homogeneousDimension : ℝ) * volume {x | ν x < 1} *
      ENNReal.ofReal (R ^ ((G.homogeneousDimension : ℝ) - β) / ((G.homogeneousDimension : ℝ) - β)) := by
  rw [power_lintegral_near_reduction_of_volumeScaling hscale hν β R,
    rpow_near_value (by linarith) hR]
  rw [show (G.homogeneousDimension : ℝ) - 1 - β + 1 = (G.homogeneousDimension : ℝ) - β by ring]

end RothschildStein.G2
