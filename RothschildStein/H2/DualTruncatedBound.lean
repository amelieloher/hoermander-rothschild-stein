-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.DualTruncatedMoment
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace RothschildStein.H2
variable {X : Type*} [MeasurableSpace X]

/-- Each clamped p-th moment is bounded from the actual
L² pairing estimates; no output Lᵖ membership is presumed
(BB p. 326). -/
theorem truncated_moment_le_of_pairing (μ : Measure X) [IsFiniteMeasure μ]
    (F : Lp ℝ 2 μ) {p q H : ℝ} (hp : 1 < p) (hq : 0 < q) (hH : 0 ≤ H)
    (hpq : (p - 1) * q = p) (hrecip : 1 / p + 1 / q = 1)
    (hpair : ∀ w : Lp ℝ 2 μ, MemLp w (ENNReal.ofReal q) μ →
      |∫ x, F x * w x ∂μ| ≤ H * (eLpNorm w (ENNReal.ofReal q) μ).toReal)
    {n : ℝ} (hn : 0 ≤ n) :
    moment μ p (fun x => min |F x| n) ≤ ENNReal.ofReal (H ^ p) := by
  have hFm : Measurable (fun x => F x) := (Lp.stronglyMeasurable F).measurable
  let g : X → ℝ := fun x => min |F x| n
  let w : X → ℝ := dualTruncation (fun x => F x) p n
  have hw2 : MemLp w 2 μ := dualTruncation_memLp μ hFm hp hn 2
  have hwq : MemLp w (ENNReal.ofReal q) μ := dualTruncation_memLp μ hFm hp hn _
  have hg : MemLp g (ENNReal.ofReal p) μ := absoluteClamp_memLp μ hFm hn _
  have hgn : ∀ x, 0 ≤ g x := fun x => le_min (abs_nonneg _) hn
  have hgint : Integrable (fun x => g x ^ p) μ := by
    have hi := hg.integrable_norm_rpow (by positivity : ENNReal.ofReal p ≠ 0) ENNReal.ofReal_ne_top
    simpa only [ENNReal.toReal_ofReal (by linarith : 0 ≤ p), Real.norm_of_nonneg (hgn _)] using hi
  have hprod : Integrable (fun x => F x * w x) μ :=
    (show MemLp (fun x => F x * w x) 1 μ from (Lp.memLp F).mul hw2).integrable (by norm_num)
  let I := ∫ x, g x ^ p ∂μ
  have hI : 0 ≤ I := integral_nonneg fun x => Real.rpow_nonneg (le_min (abs_nonneg _) hn) _
  have hmoment : moment μ p g = ENNReal.ofReal I := by
    dsimp [moment, I]
    simp only [abs_of_nonneg (hgn _)]
    exact (ofReal_integral_eq_lintegral_ofReal hgint
      (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (le_min (abs_nonneg _) hn) _)).symm
  have hnorm := (dualTruncation_norm_moment μ hFm (by linarith : 0 < p) hq hn hpq).2
  have hnorm' : (eLpNorm w (ENNReal.ofReal q) μ).toReal = I ^ (1 / q) := by
    rw [hmoment, ENNReal.toReal_ofReal hI] at hnorm
    exact hnorm
  have hroot : I ^ (1 / p) ≤ H := by
    apply dual_moment_root_le hI hH (by linarith) hrecip
    calc
      I ≤ ∫ x, F x * w x ∂μ := integral_mono hgint hprod (fun x => dualTruncation_pairing_ge hp hn x)
      _ ≤ |∫ x, F x * w x ∂μ| := le_abs_self _
      _ = |∫ x, F x * (hw2.toLp w) x ∂μ| := by
        congr 1
        apply integral_congr_ae
        filter_upwards [hw2.coeFn_toLp] with x hx
        rw [hx]
      _ ≤ H * (eLpNorm (hw2.toLp w) (ENNReal.ofReal q) μ).toReal :=
        hpair (hw2.toLp w) ((memLp_congr_ae hw2.coeFn_toLp).mpr hwq)
      _ = _ := by rw [eLpNorm_congr_ae hw2.coeFn_toLp, hnorm']
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hI _) hroot (by linarith : 0 ≤ p)
  rw [← Real.rpow_mul hI, div_mul_cancel₀ 1 (by linarith : p ≠ 0), Real.rpow_one] at hpow
  rw [hmoment]
  exact ENNReal.ofReal_le_ofReal hpow

end RothschildStein.H2
