-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.DyadicTelescoping

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open scoped BigOperators
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Every dyadic scaled kernel has the exact geometric
coefficient and shrinking argument (BB (6.27)–(6.28), pp. 265–266). -/
theorem scaledFundamentalKernel_dyadic_eq (Γ : (Fin N → ℝ) → ℝ)
    (n : ℕ) (x : Fin N → ℝ) :
    scaledFundamentalKernel G ((2 : ℝ) ^ n) Γ x =
      ((2 : ℝ) ^ (2 - (G.homogeneousDimension : ℝ))) ^ n *
        Γ (G.dilate ((1 / 2 : ℝ) ^ n) x) := by
  rw [scaledFundamentalKernel_eq_rpow G (pow_pos (by norm_num) n)]
  have hf : ((2 : ℝ) ^ n) ^ (2 - (G.homogeneousDimension : ℝ)) =
      ((2 : ℝ) ^ (2 - (G.homogeneousDimension : ℝ))) ^ n := by
    rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2),
      mul_comm (n : ℝ), Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
  have hi : ((2 : ℝ) ^ n)⁻¹ = (1 / 2 : ℝ) ^ n := by rw [← inv_pow]; norm_num
  rw [hf, hi]

/-- The scaled kernels have the exact consecutive dyadic
covariance used in passage to the global limit (BB p. 266). -/
theorem scaledFundamentalKernel_dyadic_step (Γ : (Fin N → ℝ) → ℝ)
    (n : ℕ) (x : Fin N → ℝ) :
    scaledFundamentalKernel G ((2 : ℝ) ^ (n + 1)) Γ (G.dilate 2 x) =
      (2 : ℝ) ^ (2 - (G.homogeneousDimension : ℝ)) *
        scaledFundamentalKernel G ((2 : ℝ) ^ n) Γ x := by
  rw [scaledFundamentalKernel_dyadic_eq, scaledFundamentalKernel_dyadic_eq, G2.dilate_dilate]
  have hd : (1 / 2 : ℝ) ^ (n + 1) * 2 = (1 / 2 : ℝ) ^ n := by rw [pow_succ]; ring
  rw [hd, pow_succ]
  ring

end RothschildStein.H1
