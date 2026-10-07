-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.HolderInterpolation

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
open scoped ENNReal NNReal
namespace RothschildStein.H3
variable {X : Type*} [MetricSpace X]

/-- Explicit lower-exponent norm bound from a supremum bound and a fixed
upper-exponent Hölder constant (BB pp. 381–382). -/
theorem boundedHolderNorm_le_interpolation_bound
    {a b : ℝ≥0} (ha : 0 < a) (hba : b ≤ a) (A : Set X)
    {f : X → ℝ} {M H : ℝ} (hM : 0 ≤ M) (hH : 0 ≤ H)
    (hs : ∀ x ∈ A, |f x| ≤ M)
    (hh : ∀ x ∈ A, ∀ y ∈ A, |f x - f y| ≤ H * dist x y ^ (a : ℝ)) :
    H2.boundedHolderNorm b A f ≤ ENNReal.ofReal M +
      ENNReal.ofReal ((2 * M) ^ (1 - (b : ℝ) / (a : ℝ)) *
        H ^ ((b : ℝ) / (a : ℝ))) := by
  have hS := H2.holderSup_le_of_bound hs
  have hA := H2.holderSemi_le_of_bound hH hh
  have hb : H2.BoundedHolder a A f :=
    (add_le_add hS hA).trans_lt (ENNReal.add_lt_top.mpr
      ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩)
  have hSM : (H2.holderSup A f).toReal ≤ M := by
    simpa only [ENNReal.toReal_ofReal hM] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hS
  have hAH : (H2.holderSemi a A f).toReal ≤ H := by
    simpa only [ENNReal.toReal_ofReal hH] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hA
  have ht : 0 ≤ (b : ℝ) / (a : ℝ) := div_nonneg b.coe_nonneg (show 0 ≤ (a : ℝ) from ha.le)
  have hu : 0 ≤ 1 - (b : ℝ) / (a : ℝ) :=
    sub_nonneg.mpr ((div_le_one (show 0 < (a : ℝ) from ha)).mpr hba)
  have hB := holderSemi_interpolation ha hba A f hb
  apply add_le_add hS
  exact hB.trans (ENNReal.ofReal_le_ofReal (mul_le_mul
    (Real.rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_left hSM (by norm_num)) hu)
    (Real.rpow_le_rpow ENNReal.toReal_nonneg hAH ht)
    (by positivity) (by positivity)))

end RothschildStein.H3
