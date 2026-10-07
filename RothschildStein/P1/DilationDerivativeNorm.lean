-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.KernelEstimatesHomogeneous

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace RothschildStein.P1

/-- A large coordinate dilation has operator norm
at most its scale raised to the largest retained coordinate weight. -/
theorem norm_kdilateCLM_le_pow {N : ℕ} (G : HomogeneousGroup N)
    (W : ℕ) (hW : ∀ j, G.weight j ≤ W) {r : ℝ} (hr : 1 ≤ r) :
    ‖kdilateCLM G r‖ ≤ r ^ W := by
  have hr0 : 0 ≤ r := zero_le_one.trans hr
  apply (kdilateCLM G r).opNorm_le_bound (pow_nonneg hr0 _)
  intro u
  rw [kdilateCLM_apply]
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (pow_nonneg hr0 _) (norm_nonneg u))).mpr
  intro j
  change ‖r ^ G.weight j * u j‖ ≤ r ^ W * ‖u‖
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hr0 _)]
  exact mul_le_mul (pow_le_pow_right₀ hr (hW j)) (norm_le_pi_norm u j)
    (norm_nonneg _) (pow_nonneg hr0 _)

end RothschildStein.P1
