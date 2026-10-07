-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.BallMeasures

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal

namespace RothschildStein.H2

/-- The ceiling costs at most one extra doubling factor; BB (7.3), p. 296,
requires this factor. -/
theorem ceiling_power_le {C t : ℝ} (hC : 1 < C) (ht : 1 ≤ t) :
    C ^ ⌈Real.logb 2 t⌉₊ ≤ C * t ^ Real.logb 2 C := by
  have hCp : 0 < C := lt_trans (by norm_num) hC
  have htp : 0 < t := zero_lt_one.trans_le ht
  have hn := Nat.ceil_lt_add_one (Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) ht)
  have he : C ^ (Real.logb 2 t) = t ^ Real.logb 2 C := by
    rw [Real.rpow_def_of_pos hCp, Real.rpow_def_of_pos htp]
    congr 1
    simp only [Real.logb]
    ring
  calc
    C ^ ⌈Real.logb 2 t⌉₊ = C ^ (⌈Real.logb 2 t⌉₊ : ℝ) := (Real.rpow_natCast _ _).symm
    _ ≤ C ^ (Real.logb 2 t + 1) := Real.rpow_le_rpow_of_exponent_le hC.le hn.le
    _ = C * t ^ Real.logb 2 C := by rw [Real.rpow_add hCp, Real.rpow_one, he, mul_comm]

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Corrected real-power growth on the full patch range. -/
theorem DoublingPatch.compare_rpow (P : DoublingPatch X) {z : X} (hz : z ∈ P.S)
    {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s) (hκ : s ≤ 6 * P.ρ) :
    P.μ (ball z s) ≤ ENNReal.ofReal (P.C_D * (s / r) ^ Real.logb 2 P.C_D) *
      P.μ (ball z r) := by
  refine (P.compare hz hr hrs hκ).trans ?_
  apply mul_le_mul_left
  rw [← ENNReal.ofReal_pow (by linarith [P.one_lt_C_D] : 0 ≤ P.C_D)]
  exact ENNReal.ofReal_le_ofReal (ceiling_power_le P.one_lt_C_D
    ((le_div_iff₀ hr).mpr (by simpa using hrs)))

/-- Shell integral of reciprocal volume, with integer doubling constant.
BB (7.4), pp. 296–297. This form also permits a closed inner shell boundary. -/
theorem DoublingPatch.shell_integral (P : DoublingPatch X) {z : X} (hz : z ∈ P.S)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 6 * P.ρ) :
    (∫⁻ y in {y | a ≤ dist z y ∧ dist z y < b}, (volumeAt P.μ z y)⁻¹ ∂P.μ) ≤
      ENNReal.ofReal P.C_D ^ ⌈Real.logb 2 (b / a)⌉₊ := by
  have hpos := (P.doubling z hz a ha (hab.trans hb)).1
  have hfin := (P.doubling z hz a ha (hab.trans hb)).2.1
  calc
    _ ≤ ∫⁻ _y in {y | a ≤ dist z y ∧ dist z y < b}, (P.μ (ball z a))⁻¹ ∂P.μ := by
      apply setLIntegral_mono measurable_const
      intro y hy
      exact ENNReal.inv_le_inv.mpr (measure_mono (ball_subset_ball hy.1))
    _ = (P.μ (ball z a))⁻¹ * P.μ {y | a ≤ dist z y ∧ dist z y < b} := setLIntegral_const _ _
    _ ≤ (P.μ (ball z a))⁻¹ * P.μ (ball z b) := by
      apply mul_le_mul_right
      apply measure_mono
      intro y hy
      simpa [mem_ball, dist_comm] using hy.2
    _ ≤ (P.μ (ball z a))⁻¹ *
        (ENNReal.ofReal P.C_D ^ ⌈Real.logb 2 (b / a)⌉₊ * P.μ (ball z a)) :=
      mul_le_mul_right (P.compare hz ha hab hb) _
    _ = ENNReal.ofReal P.C_D ^ ⌈Real.logb 2 (b / a)⌉₊ := by
      rw [mul_left_comm, ENNReal.inv_mul_cancel (ne_of_gt hpos) (ne_of_lt hfin), mul_one]

/-- The real-power shell bound with the corrected doubling prefactor. -/
theorem DoublingPatch.shell_integral_rpow (P : DoublingPatch X) {z : X} (hz : z ∈ P.S)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 6 * P.ρ) :
    (∫⁻ y in {y | a ≤ dist z y ∧ dist z y < b}, (volumeAt P.μ z y)⁻¹ ∂P.μ) ≤
      ENNReal.ofReal (P.C_D * (b / a) ^ Real.logb 2 P.C_D) := by
  refine (P.shell_integral hz ha hab hb).trans ?_
  rw [← ENNReal.ofReal_pow (by linarith [P.one_lt_C_D] : 0 ≤ P.C_D)]
  exact ENNReal.ofReal_le_ofReal (ceiling_power_le P.one_lt_C_D
    ((le_div_iff₀ ha).mpr (by simpa using hab)))

end RothschildStein.H2
