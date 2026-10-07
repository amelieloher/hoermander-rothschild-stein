-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.ShellDomination

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The endpoint annulus of ratio four needs exactly two doublings,
without the extra prefactor of the real-power shell bound. BB p. 303. -/
theorem DoublingPatch.shell_integral_pow (P : DoublingPatch X) {z : X} (hz : z ∈ P.S)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 6 * P.ρ) (n : ℕ) (hn : b ≤ 2 ^ n * a) :
    (∫⁻ y in {y | a ≤ dist z y ∧ dist z y < b}, (volumeAt P.μ z y)⁻¹ ∂P.μ) ≤
      ENNReal.ofReal P.C_D ^ n := by
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
        (ENNReal.ofReal P.C_D ^ n * P.μ (ball z a)) :=
      mul_le_mul_right (P.compare_pow hz ha (ha.trans_le hab) hb n hn) _
    _ = ENNReal.ofReal P.C_D ^ n := by
      rw [mul_left_comm, ENNReal.inv_mul_cancel (ne_of_gt hpos) (ne_of_lt hfin), mul_one]

end RothschildStein.H2
