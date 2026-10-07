-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.FiberChartVolumeBounds
public import RothschildStein.L1.MeasureRatioBounds

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace RothschildStein.L1

/-- For finite volumes and a positive original volume, the
real quotient in GaugeFiberData is exactly the measured ENNReal quotient
(BB pp. 521–522; no normalization factor is suppressed). -/
theorem ofReal_volume_toReal_ratio {n N : ℕ}
    (A : Set (Fin n → ℝ)) (B : Set (Fin N → ℝ))
    (hA : volume A ≠ ⊤) (hB : volume B ≠ ⊤) (hpos : 0 < (volume A).toReal) :
    ENNReal.ofReal ((volume B).toReal / (volume A).toReal) = volume B / volume A := by
  rw [ENNReal.ofReal_div_of_pos hpos,ENNReal.ofReal_toReal hB,ENNReal.ofReal_toReal hA]

/-- Combine the full two-sided completed-frame measure ratio
with raw chart fiber bounds. Both the small original determinant and the
exact real volume quotient are retained in the density bounds.
The ratio premise is the output of completed_frame_ball_measure_ratio;
chart construction and scale selection are supplied separately
(BB pp. 520–522, (10.49), repaired lower determinant ratio). -/
theorem fiber_density_bounds_of_frame_measure_ratio {n m : ℕ}
    (A : Set (Fin n → ℝ)) (B Small Large : Set (Fin (n+m) → ℝ))
    (hA : volume A ≠ ⊤) (hB : volume B ≠ ⊤) (hpos : 0 < (volume A).toReal)
    {R α β c C : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hc : 0 < c) (hC : 0 < C)
    (hratio : ENNReal.ofReal c * ENNReal.ofReal R ≤ volume B / volume A ∧
      volume B / volume A ≤ ENNReal.ofReal C * ENNReal.ofReal R)
    (y : Fin n → ℝ)
    (hlower : ENNReal.ofReal (α*R) ≤ fiberVolume Large y)
    (hupper : fiberVolume Small y ≤ ENNReal.ofReal (β*R)) :
    ENNReal.ofReal ((α/C) * (volume B).toReal / (volume A).toReal) ≤ fiberVolume Large y ∧
      fiberVolume Small y ≤ ENNReal.ofReal ((β/c) * (volume B).toReal / (volume A).toReal) := by
  have hlo := mul_le_mul_right hratio.2 (ENNReal.ofReal (α/C))
  have hhi := mul_le_mul_right hratio.1 (ENNReal.ofReal (β/c))
  have helo : ENNReal.ofReal (α/C) * (ENNReal.ofReal C * ENNReal.ofReal R) =
      ENNReal.ofReal (α*R) := by
    rw [← mul_assoc,← ENNReal.ofReal_mul (div_nonneg hα hC.le)]
    have he : (α/C)*C = α := div_mul_cancel₀ α hC.ne'
    rw [he,← ENNReal.ofReal_mul hα]
  have hehi : ENNReal.ofReal (β/c) * (ENNReal.ofReal c * ENNReal.ofReal R) =
      ENNReal.ofReal (β*R) := by
    rw [← mul_assoc,← ENNReal.ofReal_mul (div_nonneg hβ hc.le)]
    have he : (β/c)*c = β := div_mul_cancel₀ β hc.ne'
    rw [he,← ENNReal.ofReal_mul hβ]
  have hl : ENNReal.ofReal (α/C) * (volume B / volume A) ≤ fiberVolume Large y := by
    rw [helo] at hlo
    exact hlo.trans hlower
  have hu : fiberVolume Small y ≤ ENNReal.ofReal (β/c) * (volume B / volume A) := by
    rw [hehi] at hhi
    exact hupper.trans hhi
  have he (q : ℝ) (hq : 0 ≤ q) :
      ENNReal.ofReal (q*(volume B).toReal/(volume A).toReal) =
        ENNReal.ofReal q * (volume B / volume A) := by
    rw [mul_div_assoc,ENNReal.ofReal_mul hq,ofReal_volume_toReal_ratio A B hA hB hpos]
  rw [he _ (div_nonneg hα hC.le),he _ (div_nonneg hβ hc.le)]
  exact ⟨hl,hu⟩

end RothschildStein.L1
