-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.LpBounds

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace RothschildStein.H2
variable {X : Type*} [MeasurableSpace X]

/-- The bounded dual test for the p > 2 estimate. -/
def dualTruncation (f : X → ℝ) (p n : ℝ) (x : X) : ℝ :=
  if 0 ≤ f x then (min |f x| n) ^ (p - 1) else -((min |f x| n) ^ (p - 1))

/-- The dual truncation is measurable (BB p. 326). -/
theorem measurable_dualTruncation {f : X → ℝ} (hf : Measurable f) (p n : ℝ) :
    Measurable (dualTruncation f p n) := by
  have hm : Measurable (fun x => min |f x| n) := by simpa only [Real.norm_eq_abs] using hf.norm.min measurable_const
  exact (hm.pow_const (p - 1)).ite (measurableSet_le measurable_const hf) (hm.pow_const (p - 1)).neg

/-- The dual truncation is bounded in every Lᵖ space of a
finite measure (BB p. 326). -/
theorem dualTruncation_memLp (μ : Measure X) [IsFiniteMeasure μ]
    {f : X → ℝ} (hf : Measurable f) {p n : ℝ} (hp : 1 < p) (hn : 0 ≤ n) (q : ℝ≥0∞) :
    MemLp (dualTruncation f p n) q μ := by
  apply MemLp.of_bound (measurable_dualTruncation hf p n).aestronglyMeasurable (n ^ (p - 1))
  apply Filter.Eventually.of_forall
  intro x
  have hmin : 0 ≤ min |f x| n := le_min (abs_nonneg _) hn
  have hpow : 0 ≤ (min |f x| n) ^ (p - 1) := Real.rpow_nonneg hmin _
  have hle : (min |f x| n) ^ (p - 1) ≤ n ^ (p - 1) :=
    Real.rpow_le_rpow hmin (min_le_right _ _) (by linarith)
  unfold dualTruncation
  split_ifs <;> simpa only [Real.norm_eq_abs, abs_neg, abs_of_nonneg hpow] using hle

omit [MeasurableSpace X] in
/-- The dual test has the exact q-th power of the truncated
p-th moment (BB p. 326). -/
theorem dualTruncation_abs_rpow {f : X → ℝ} {p q n : ℝ}
    (hn : 0 ≤ n) (hpq : (p - 1) * q = p) (x : X) :
    |dualTruncation f p n x| ^ q = (min |f x| n) ^ p := by
  have hmin : 0 ≤ min |f x| n := le_min (abs_nonneg _) hn
  have hpow := Real.rpow_nonneg hmin (p - 1)
  unfold dualTruncation
  split_ifs <;> simp only [abs_neg, abs_of_nonneg hpow]
    <;> rw [← Real.rpow_mul hmin, hpq]

omit [MeasurableSpace X] in
/-- Pairing with the test dominates the truncated p-th power
(BB p. 326). -/
theorem dualTruncation_pairing_ge {f : X → ℝ} {p n : ℝ}
    (hp : 1 < p) (hn : 0 ≤ n) (x : X) :
    (min |f x| n) ^ p ≤ f x * dualTruncation f p n x := by
  let a := min |f x| n
  have ha : 0 ≤ a := le_min (abs_nonneg _) hn
  have hpow : 0 ≤ a ^ (p - 1) := Real.rpow_nonneg ha _
  have heq : a ^ p = a * a ^ (p - 1) := by
    calc
      a ^ p = a ^ (1 + (p - 1)) := by congr 1; ring
      _ = a ^ (1 : ℝ) * a ^ (p - 1) := Real.rpow_add' ha (by linarith : 1 + (p - 1) ≠ 0)
      _ = _ := by rw [Real.rpow_one]
  have hle : a ^ p ≤ |f x| * a ^ (p - 1) := by
    rw [heq]
    exact mul_le_mul_of_nonneg_right (min_le_left _ _) hpow
  dsimp [a] at hle
  unfold dualTruncation
  split_ifs with h
  · simpa only [abs_of_nonneg h] using hle
  · simpa only [abs_of_neg (lt_of_not_ge h), neg_mul, mul_neg] using hle

end RothschildStein.H2
