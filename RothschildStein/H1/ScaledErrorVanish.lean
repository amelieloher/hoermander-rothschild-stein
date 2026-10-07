-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.KernelScaling
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Normed.Group.Bounded

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Positive weights give the uniform contraction bound
needed on the support of a test (BB p. 266). -/
theorem norm_dilate_le_mul {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (x : Fin N → ℝ) :
    ‖G.dilate t x‖ ≤ t * ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg ht (norm_nonneg x))).mpr
  intro j
  change ‖t ^ G.weight j * x j‖ ≤ _
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ht _)]
  have hp : t ^ G.weight j ≤ t := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (G.weight_pos j))
    rw [hk, pow_succ]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (pow_le_one₀ ht ht1 : t ^ k ≤ 1) ht
  exact (mul_le_mul_of_nonneg_right hp (norm_nonneg _)).trans
    (mul_le_mul_of_nonneg_left (norm_le_pi_norm x j) ht)

/-- A scaled error which vanishes near zero eventually has zero
pairing with every compactly supported test (BB p. 266; explicit uniform
compact-support argument). No differentiability of the test is required. -/
theorem eventually_integral_scaledError_zero
    (E φ : (Fin N → ℝ) → ℝ) (hs : HasCompactSupport φ)
    (hE : E =ᶠ[𝓝 (0 : Fin N → ℝ)] 0) :
    ∀ᶠ n : ℕ in atTop, (∫ x, scaledErrorKernel G ((2 : ℝ) ^ n) E x * φ x) = 0 := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hE
  obtain ⟨R, hR⟩ := hs.isBounded.exists_norm_le
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).mul_const R
  simp only [zero_mul] at ht
  have hevent : ∀ᶠ n : ℕ in atTop, (1 / 2 : ℝ) ^ n * R < r :=
    ht.eventually (gt_mem_nhds hr)
  filter_upwards [hevent] with n hn
  apply integral_eq_zero_of_ae
  apply Eventually.of_forall
  intro x
  change scaledErrorKernel G ((2 : ℝ) ^ n) E x * φ x = 0
  by_cases hx : φ x = 0
  · rw [hx, mul_zero]
  · have hxR : ‖x‖ ≤ R := hR x (subset_closure hx)
    have hnorm : ‖G.dilate ((2 : ℝ) ^ n)⁻¹ x‖ < r := by
      have hi : ((2 : ℝ) ^ n)⁻¹ = (1 / 2 : ℝ) ^ n := by rw [← inv_pow]; norm_num
      rw [hi]
      exact ((norm_dilate_le_mul G (pow_nonneg (by norm_num) _)
        (pow_le_one₀ (by norm_num) (by norm_num)) x).trans
        (mul_le_mul_of_nonneg_left hxR (pow_nonneg (by norm_num) _))).trans_lt hn
    have hz := hball (by simpa only [Metric.mem_ball, dist_zero_right] using hnorm)
    change E (G.dilate ((2 : ℝ) ^ n)⁻¹ x) = 0 at hz
    simp only [scaledErrorKernel, hz, mul_zero, zero_mul]

end RothschildStein.H1
