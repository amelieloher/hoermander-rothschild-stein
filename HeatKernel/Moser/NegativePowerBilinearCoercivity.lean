-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.CaccioppoliBilinearAbsorption
public import HeatKernel.Moser.NegativePowerFluxCoercivity
import all Mathlib.Basic.Real.Basic

/-! Coercivity of reciprocal-power flux in the symmetric coefficient form. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
open MeasureTheory
namespace HeatKernel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Symmetric positive coefficient forms absorb the reciprocal-power mixed flux
while retaining half the principal term and its exact cutoff coefficient. -/
theorem negative_power_bilinear_absorption
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hsym : ∀ v w, B v w = B w v)
    (hpos : ∀ v, 0 ≤ B v v) {p s : ℝ} (hp : 0 < p) (hs : 0 < s)
    (η : ℝ) (g d : E) :
    (p + 1) / 2 * s ^ (-p - 2) * η ^ 2 * B g g -
      (2 / (p + 1)) * s ^ (-p) * B d d ≤
      (p + 1) * s ^ (-p - 2) * η ^ 2 * B g g -
        2 * s ^ (-p - 1) * η * B g d := by
  have hpow : s ^ (-p - 2) * s ^ 2 = s ^ (-p) := by
    rw [← Real.rpow_natCast s 2, ← Real.rpow_add hs]
    congr 1
    ring
  have hlin : s ^ (-p - 2) * s = s ^ (-p - 1) := by
    calc
      _ = s ^ (-p - 2) * s ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by
        rw [← Real.rpow_add hs]
        congr 1
        ring
  have h := caccioppoli_weighted_bilinear_absorption B hsym hpos
    (by linarith : 0 < p + 1) (Real.rpow_nonneg hs.le (-p - 2)) (-s) η g d
  have he : 2 * s ^ (-p - 2) * (-s) ^ 2 / (p + 1) =
      (2 / (p + 1)) * s ^ (-p) := by
    rw [neg_sq, ← hpow]
    ring
  have hm : 2 * s ^ (-p - 2) * (-s) = -2 * s ^ (-p - 1) := by
    rw [← hlin]
    ring
  rw [he, hm] at h
  convert h using 1 <;> ring

end HeatKernel
