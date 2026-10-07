-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.HolderSpaces

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Metric
open scoped ENNReal NNReal
namespace RothschildStein.H3
variable {X : Type*} [MetricSpace X]

/-- The short/long distance split upgrades a scaled
mean-value estimate to the exact Hölder power (BB Lemma 8.54, p. 384).
This applies equally to the empty word and each fixed derivative word. -/
theorem scaled_cutoff_holder_difference {f : X → ℝ} {M a : ℝ}
    (hM : 0 ≤ M) (ha : 0 < a) {α : ℝ≥0} (hα1 : (α : ℝ) ≤ 1)
    (hb : ∀ x, |f x| ≤ M)
    (hd : ∀ x y, |f x - f y| ≤ M * (dist x y / a + (dist x y / a) ^ 2))
    (x y : X) :
    |f x - f y| ≤ (2 * M / a ^ (α : ℝ)) * dist x y ^ (α : ℝ) := by
  let t := dist x y / a
  have ht : 0 ≤ t := div_nonneg dist_nonneg ha.le
  have hfactor : 2 * M * t ^ (α : ℝ) =
      (2 * M / a ^ (α : ℝ)) * dist x y ^ (α : ℝ) := by
    dsimp [t]
    rw [Real.div_rpow dist_nonneg ha.le]
    ring
  apply le_trans _ hfactor.le
  by_cases ht1 : t ≤ 1
  · have htα : t ≤ t ^ (α : ℝ) := Real.self_le_rpow_of_le_one ht ht1 hα1
    have ht2 : t ^ 2 ≤ t := by nlinarith
    calc
      _ ≤ M * (t + t ^ 2) := hd x y
      _ ≤ 2 * M * t := by nlinarith
      _ ≤ 2 * M * t ^ (α : ℝ) := mul_le_mul_of_nonneg_left htα (by positivity)
  · have htα : 1 ≤ t ^ (α : ℝ) := Real.one_le_rpow (le_of_not_ge ht1) α.coe_nonneg
    calc
      _ ≤ |f x| + |f y| := by simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (f x) (-f y)
      _ ≤ 2 * M := by linarith [hb x, hb y]
      _ ≤ 2 * M * t ^ (α : ℝ) := le_mul_of_one_le_right (by positivity) htα

/-- The resulting exact global seminorm bound. -/
theorem scaled_cutoff_holderSemi_le {f : X → ℝ} {M a : ℝ}
    (hM : 0 ≤ M) (ha : 0 < a) {α : ℝ≥0} (hα1 : (α : ℝ) ≤ 1)
    (hb : ∀ x, |f x| ≤ M)
    (hd : ∀ x y, |f x - f y| ≤ M * (dist x y / a + (dist x y / a) ^ 2)) :
    H2.holderSemi α univ f ≤ ENNReal.ofReal (2 * M / a ^ (α : ℝ)) :=
  H2.holderSemi_le_of_bound (by positivity)
    (fun x _ y _ => scaled_cutoff_holder_difference hM ha hα1 hb hd x y)

/-- Adding the supremum gives the full global norm. -/
theorem scaled_cutoff_holderNorm_le {f : X → ℝ} {M a : ℝ}
    (hM : 0 ≤ M) (ha : 0 < a) {α : ℝ≥0} (hα1 : (α : ℝ) ≤ 1)
    (hb : ∀ x, |f x| ≤ M)
    (hd : ∀ x y, |f x - f y| ≤ M * (dist x y / a + (dist x y / a) ^ 2)) :
    H2.boundedHolderNorm α univ f ≤ ENNReal.ofReal (M + 2 * M / a ^ (α : ℝ)) := by
  exact (add_le_add (H2.holderSup_le_of_bound (fun x _ => hb x))
    (scaled_cutoff_holderSemi_le hM ha hα1 hb hd)).trans_eq
      (ENNReal.ofReal_add hM (by positivity)).symm

end RothschildStein.H3
