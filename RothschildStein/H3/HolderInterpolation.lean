-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.HolderOperations

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Metric
open scoped ENNReal NNReal
namespace RothschildStein.H3
variable {X : Type*} [MetricSpace X]

/-- The precise C⁰/Cα interpolation bound on any subset,
with factor 2 from the supremum bound and no domain geometry assumption
(BB pp. 84–86). -/
theorem holderSemi_interpolation {a b : ℝ≥0} (ha : 0 < a) (hba : b ≤ a)
    (A : Set X) (f : X → ℝ) (hf : H2.BoundedHolder a A f) :
    H2.holderSemi b A f ≤ ENNReal.ofReal
      ((2 * (H2.holderSup A f).toReal) ^ (1 - (b : ℝ) / (a : ℝ)) *
        (H2.holderSemi a A f).toReal ^ ((b : ℝ) / (a : ℝ))) := by
  have haR : 0 < (a : ℝ) := ha
  let t := (b : ℝ) / (a : ℝ)
  have ht0 : 0 ≤ t := div_nonneg b.coe_nonneg haR.le
  have ht1 : t ≤ 1 := (div_le_one haR).mpr hba
  have hA : 0 ≤ 2 * (H2.holderSup A f).toReal := by positivity
  have hB : 0 ≤ (H2.holderSemi a A f).toReal := ENNReal.toReal_nonneg
  apply H2.holderSemi_le_of_bound (mul_nonneg (Real.rpow_nonneg hA _)
    (Real.rpow_nonneg hB _))
  intro x hx y hy
  have hu : |f x - f y| ≤ 2 * (H2.holderSup A f).toReal := by
    calc
      _ ≤ |f x| + |f y| := by
        simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (f x) (-f y)
      _ ≤ _ := by
        have hx' := H2.abs_le_holderSup hf.parts.1 hx
        have hy' := H2.abs_le_holderSup hf.parts.1 hy
        linarith
  have hd := H2.sub_le_holderSemi hf.parts.2 hx hy
  have he : |f x - f y| = |f x - f y| ^ (1 - t) * |f x - f y| ^ t := by
    rw [← Real.rpow_add' (abs_nonneg _) (by linarith : (1 - t) + t ≠ 0)]
    simp only [sub_add_cancel, Real.rpow_one]
  calc
    _ = _ := he
    _ ≤ (2 * (H2.holderSup A f).toReal) ^ (1 - t) *
        ((H2.holderSemi a A f).toReal * dist x y ^ (a : ℝ)) ^ t :=
      mul_le_mul (Real.rpow_le_rpow (abs_nonneg _) hu (sub_nonneg.mpr ht1))
        (Real.rpow_le_rpow (abs_nonneg _) hd ht0)
        (Real.rpow_nonneg (abs_nonneg _) _) (Real.rpow_nonneg hA _)
    _ = _ := by
      rw [Real.mul_rpow hB (Real.rpow_nonneg dist_nonneg _),
        ← Real.rpow_mul dist_nonneg]
      have hat : (a : ℝ) * t = (b : ℝ) := by dsimp [t]; field_simp
      rw [hat, mul_assoc]

end RothschildStein.H3
