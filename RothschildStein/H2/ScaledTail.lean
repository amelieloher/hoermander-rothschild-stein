-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.VolumeIntegrals

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The cancellation radius cancels exactly against the tail
integral, leaving the factor 4⁻ᵝ (BB p. 320, corrected radius cap). -/
theorem DoublingPatch.scaled_outer_volume_integral (P : DoublingPatch X)
    {z : X} (hz : z ∈ P.S) {β r σ : ℝ} (hβ : 0 < β) (hr : 0 < r)
    (hrσ : 4 * r ≤ σ) (hσρ : σ ≤ 6 * P.ρ) :
    ENNReal.ofReal (r ^ β) *
      (∫⁻ y in ball z σ \ ball z (4 * r),
        ENNReal.ofReal (dist z y ^ (-β)) * (volumeAt P.μ z y)⁻¹ ∂P.μ) ≤
      ENNReal.ofReal (volumeIntegralConstant P.C_D β * (4 : ℝ) ^ (-β)) := by
  have htail := P.outer_volume_integral hz hβ (by positivity : 0 < 4 * r) hrσ hσρ
  have he : r ^ β * (volumeIntegralConstant P.C_D β * (4 * r) ^ (-β)) =
      volumeIntegralConstant P.C_D β * (4 : ℝ) ^ (-β) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hr.le]
    calc
      _ = (volumeIntegralConstant P.C_D β * (4 : ℝ) ^ (-β)) * (r ^ β * r ^ (-β)) := by ring
      _ = _ := by rw [← Real.rpow_add hr]; simp
  calc
    _ ≤ ENNReal.ofReal (r ^ β) *
        ENNReal.ofReal (volumeIntegralConstant P.C_D β * (4 * r) ^ (-β)) := mul_le_mul' le_rfl htail
    _ = _ := by rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hr.le _), he]

end RothschildStein.H2
