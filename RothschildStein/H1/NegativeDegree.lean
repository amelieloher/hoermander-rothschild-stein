-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.DyadicSeries
public import RothschildStein.H1.DyadicRigidity
public import RothschildStein.Definitions.HomogeneousGroup.homogeneousDimension

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- The actual correction series has the required geometric
coefficient when Q > 2 (BB (6.28), p. 266). -/
theorem contDiff_fundamentalCorrectionSeries
    (hQ : 2 < (G.homogeneousDimension : ℝ))
    {ω : (Fin N → ℝ) → ℝ} (hω : ContDiff ℝ (⊤ : ℕ∞) ω) (hs : HasCompactSupport ω) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => ∑' n : ℕ,
      ((2 : ℝ) ^ (2 - (G.homogeneousDimension : ℝ))) ^ n •
        ω (G.dilate ((1 / 2 : ℝ) ^ n) x)) :=
  contDiff_dyadicSeries G hω hs
    (Real.rpow_pos_of_pos (by norm_num) _).le
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))

/-- A continuous representative with the actual fundamental
solution's negative dyadic degree is zero (BB p. 266). -/
theorem eq_zero_of_fundamental_dyadic_degree
    (hQ : 2 < (G.homogeneousDimension : ℝ))
    {f : (Fin N → ℝ) → ℝ} (hf : ContinuousAt f 0)
    (hscale : ∀ x, f (G.dilate 2 x) =
      (2 : ℝ) ^ (2 - (G.homogeneousDimension : ℝ)) * f x) : f = 0 :=
  eq_zero_of_dyadic_scaling G hf
    (Real.rpow_pos_of_pos (by norm_num) _).le
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)) hscale

end RothschildStein.H1
