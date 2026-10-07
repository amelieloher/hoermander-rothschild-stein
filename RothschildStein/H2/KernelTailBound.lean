-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.KernelCancellation
public import RothschildStein.H2.ScaledTail

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Extended-real form of the transposed smoothness estimate,
using the positive finite ball volume supplied by local doubling. -/
theorem DoublingPatch.transpose_difference_enorm (P : DoublingPatch X)
    {E : Set X} {β A S r : ℝ} {K : X → X → ℝ}
    (hKt : KernelClass P.μ E β 0 A S (fun x y => K y x))
    {z x y : X} (hzS : z ∈ P.S) (hz : z ∈ E) (hx : x ∈ E) (hy : y ∈ E)
    (hr : 0 < r) (hxr : dist z x < r) (hyr : 4 * r ≤ dist z y)
    (hyρ : dist z y ≤ 6 * P.ρ) :
    ‖K y x - K y z‖ₑ ≤ ENNReal.ofReal S * ENNReal.ofReal (r ^ β) *
      (ENNReal.ofReal (dist z y ^ (-β)) * (volumeAt P.μ z y)⁻¹) := by
  have hd : 0 < dist z y := by linarith
  have hv := P.doubling z hzS (dist z y) hd hyρ
  have hvp : 0 < (volumeAt P.μ z y).toReal := ENNReal.toReal_pos hv.1.ne' hv.2.1.ne
  have hb := hKt.transpose_difference_bound hz hx hy hr hxr hyr
  have he : ENNReal.ofReal (kernelWeight P.μ 0 z y) = (volumeAt P.μ z y)⁻¹ := by
    rw [kernelWeight, Real.rpow_zero, ENNReal.ofReal_div_of_pos hvp,
      ENNReal.ofReal_one, ENNReal.ofReal_toReal (a := volumeAt P.μ z y) hv.2.1.ne, one_div]
  have hp : (r / dist z y) ^ β = r ^ β * dist z y ^ (-β) := by
    rw [Real.div_rpow hr.le hd.le, Real.rpow_neg hd.le]
    simp only [div_eq_mul_inv]
  calc
    _ ≤ ENNReal.ofReal (S * kernelWeight P.μ 0 z y * (r / dist z y) ^ β) := by
      simpa only [← ofReal_norm, Real.norm_eq_abs] using ENNReal.ofReal_le_ofReal hb
    _ = _ := by
      rw [ENNReal.ofReal_mul (mul_nonneg hKt.S_nonneg (kernelWeight_nonneg _ _ _ _)),
        ENNReal.ofReal_mul hKt.S_nonneg, he, hp,
        ENNReal.ofReal_mul (Real.rpow_nonneg hr.le _)]
      ac_rfl

end RothschildStein.H2
