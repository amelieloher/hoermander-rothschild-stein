-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.OperatorEnergy
public import RothschildStein.H2.WeakEnergy
public import RothschildStein.H2.LpBounds

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace RothschildStein.H2
variable {X : Type*} [MeasurableSpace X]

/-- Identify the weak-(1,1) endpoint norm with the moment
used in interpolation (BB p. 326). -/
theorem moment_one_eq_eLpNorm (μ : Measure X) {f : X → ℝ} (hf : AEStronglyMeasurable f μ) :
    moment μ 1 f = eLpNorm f 1 μ := by
  rw [eLpNorm_one_eq_lintegral_enorm hf]
  apply lintegral_congr
  intro x
  simp only [Real.rpow_one, ← Real.norm_eq_abs, ofReal_norm]

/-- The second moment is precisely the squared L² integral
(BB p. 326). -/
theorem moment_two_eq_square_integral (μ : Measure X) (f : X → ℝ) :
    moment μ 2 f = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
  apply lintegral_congr
  intro x
  rw [Real.rpow_two, ← Real.norm_eq_abs, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- The L² operator norm gives the weak-(2,2) endpoint
with constant cT² (BB p. 326). -/
theorem operator_weak_two_two (μ : Measure X) (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    {cT : ℝ} (hcT : ‖T‖ ≤ cT) (v : Lp ℝ 2 μ) {t : ℝ} (ht : 0 < t) :
    distribution μ (fun x => (T v) x) t ≤ ENNReal.ofReal (cT ^ 2 / t ^ (2 : ℝ)) * moment μ 2 v := by
  have hc0 : 0 ≤ cT := (norm_nonneg T).trans hcT
  calc
    _ ≤ (ENNReal.ofReal (t ^ 2))⁻¹ * ∫⁻ x, ‖(T v) x‖ₑ ^ 2 ∂μ :=
      distribution_le_square_integral μ _ (Lp.aestronglyMeasurable _).aemeasurable ht
    _ ≤ (ENNReal.ofReal (t ^ 2))⁻¹ * (ENNReal.ofReal cT ^ 2 * ∫⁻ x, ‖v x‖ₑ ^ 2 ∂μ) :=
      mul_le_mul' le_rfl (operator_square_integral_le μ T hcT v)
    _ = _ := by
      rw [moment_two_eq_square_integral, Real.rpow_two,
        ENNReal.ofReal_div_of_pos (sq_pos_of_pos ht), ← ENNReal.ofReal_pow hc0]
      simp only [div_eq_mul_inv]
      ac_rfl

end RothschildStein.H2
