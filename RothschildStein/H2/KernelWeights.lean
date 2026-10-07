-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.KernelClass
public import RothschildStein.H2.Patches

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Metric

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [BorelSpace X] in
/-- Separate the fractional power from the singular radial weight. -/
theorem kernelWeight_eq_mul (μ : Measure X) (ν : ℝ) (x y : X) :
    kernelWeight μ ν x y = dist x y ^ ν * kernelWeight μ 0 x y := by
  simp only [kernelWeight, Real.rpow_zero]
  ring

/-- Compare the radial weights at nearby centers.
BB (7.8), p. 300, using the volume comparison for nearby balls. -/
theorem DoublingPatch.kernelWeight_compare (P : DoublingPatch X) {ν : ℝ} (hν : 0 ≤ ν)
    {x₀ x y : X} (hx₀ : x₀ ∈ P.S) (hx : x ∈ P.S)
    (hs : 2 * dist x₀ x < dist x₀ y) (hr : dist x₀ y ≤ 4 * P.ρ) :
    kernelWeight P.μ ν x y ≤ (3 / 2 : ℝ) ^ ν * P.C_D ^ 2 * kernelWeight P.μ ν x₀ y := by
  have hd₀ : 0 < dist x₀ y := by have := dist_nonneg (x := x₀) (y := x); linarith
  have hd : 0 < dist x y := by
    have := (distance_comparison hs).2
    linarith
  have hdist : dist x y ≤ (3 / 2 : ℝ) * dist x₀ y := by
    have := (distance_comparison hs).1
    linarith
  have hrx : dist x y ≤ 6 * P.ρ := by nlinarith [P.ρ_pos]
  have hv₀ := P.doubling x₀ hx₀ (dist x₀ y) hd₀ (by linarith [P.ρ_pos])
  have hv := P.doubling x hx (dist x y) hd hrx
  have hv₀p : 0 < (volumeAt P.μ x₀ y).toReal := ENNReal.toReal_pos hv₀.1.ne' hv₀.2.1.ne
  have hvp : 0 < (volumeAt P.μ x y).toReal := ENNReal.toReal_pos hv.1.ne' hv.2.1.ne
  have hc : 0 ≤ P.C_D := le_of_lt (lt_trans (by norm_num) P.one_lt_C_D)
  have hvc : (volumeAt P.μ x₀ y).toReal ≤ P.C_D ^ 2 * (volumeAt P.μ x y).toReal := by
    have he := ENNReal.toReal_mono
      (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hv.2.1.ne)
      (P.volume_compare_left hx hs hr)
    simpa [volumeAt, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hc] using he
  have hpow : dist x y ^ ν ≤ (3 / 2 : ℝ) ^ ν * dist x₀ y ^ ν := by
    simpa [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3 / 2) dist_nonneg] using
      Real.rpow_le_rpow dist_nonneg hdist hν
  unfold kernelWeight
  rw [← mul_div_assoc, div_le_div_iff₀ hvp hv₀p]
  calc
    dist x y ^ ν * (volumeAt P.μ x₀ y).toReal ≤
        ((3 / 2 : ℝ) ^ ν * dist x₀ y ^ ν) *
          (P.C_D ^ 2 * (volumeAt P.μ x y).toReal) :=
      mul_le_mul hpow hvc ENNReal.toReal_nonneg (by positivity)
    _ = _ := by ring

end RothschildStein.H2
