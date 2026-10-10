-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.LevelTruncation
public import HeatKernel.Sobolev.TailRecursion
import Mathlib.Tactic

/-!
# Weak power estimates from Nash inequalities and truncations

The form domain and energy are arbitrary. The hypotheses require the Nash
inequality on that domain, membership of each level truncation, and its energy
contraction. The conclusion is a distribution estimate on a finite measure space.
-/

@[expose] public section

open MeasureTheory Set

namespace HeatKernel.Sobolev

/-- The homogeneity calculation converting a truncated Nash estimate into a tail recursion. -/
theorem normalized_tail_step_of_truncated_nash {t m v H b p : ℝ}
    (ht : 0 < t) (hv : 0 ≤ v) (hexponent : b + p - 2 = p * b)
    (hnash : t ^ 2 * m ≤ H * (t * v) ^ b) :
    m * (2 * t) ^ p ≤ (2 ^ p * H) * (v * t ^ p) ^ b := by
  have he₁ : t ^ 2 * t ^ (p - 2) = t ^ p := by
    rw [← Real.rpow_two, ← Real.rpow_add ht]
    congr 1
    ring
  have he₂ : t ^ b * t ^ (p - 2) = t ^ (p * b) := by
    rw [← Real.rpow_add ht]
    congr 1
    linarith
  have h := mul_le_mul_of_nonneg_right hnash
    (mul_nonneg (Real.rpow_nonneg ht.le (p - 2)) (Real.rpow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) p))
  rw [Real.mul_rpow ht.le hv] at h
  have hleft : t ^ 2 * m * (t ^ (p - 2) * 2 ^ p) = m * (2 * t) ^ p := by
    rw [Real.mul_rpow (by norm_num) ht.le]
    calc
      _ = m * (t ^ 2 * t ^ (p - 2)) * 2 ^ p := by ring
      _ = _ := by rw [he₁]; ring
  have hright : H * (t ^ b * v ^ b) * (t ^ (p - 2) * 2 ^ p) =
      (2 ^ p * H) * (v * t ^ p) ^ b := by
    rw [Real.mul_rpow hv (Real.rpow_nonneg ht.le _), ← Real.rpow_mul ht.le]
    calc
      _ = (2 ^ p * H) * v ^ b * (t ^ b * t ^ (p - 2)) := by ring
      _ = _ := by rw [he₂]; ring
  rwa [hleft, hright] at h

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]

/-- A form Nash inequality and contraction under level truncation imply a weak power tail. -/
theorem measure_abs_gt_le_of_nash_truncation
    {D : Set (α → ℝ)} {energy : (α → ℝ) → ℝ} {u : α → ℝ}
    (hu : Measurable u) {N E a b : ℝ}
    (hN : 0 ≤ N) (hE : 0 ≤ E) (ha : 0 ≤ a) (hb : 0 ≤ b) (hb₁ : b < 1)
    (hnash : ∀ f ∈ D, (∀ x, 0 ≤ f x) →
      (∫ x, f x ^ 2 ∂μ) ≤ N * (energy f) ^ a * (∫ x, f x ∂μ) ^ b)
    (htrunc : ∀ t, 0 < t → levelTruncation u t ∈ D)
    (henergy : ∀ t, 0 < t → 0 ≤ energy (levelTruncation u t) ∧
      energy (levelTruncation u t) ≤ E)
    {s : ℝ} (hs : 0 < s) :
    μ.real {x | s < |u x|} ≤
      (2 ^ ((2 - b) / (1 - b)) * (N * E ^ a)) ^ (1 / (1 - b)) *
        s ^ (-((2 - b) / (1 - b))) := by
  let M : ℝ → ℝ := fun t => μ.real {x | t < |u x|}
  let p := (2 - b) / (1 - b)
  have hden : 0 < 1 - b := sub_pos.mpr hb₁
  have hp : 0 ≤ p := by
    dsimp [p]
    exact div_nonneg (by linarith) hden.le
  have hhom : b + p - 2 = p * b := by
    dsimp [p]
    have hbne : 1 - b ≠ 0 := by linarith
    field_simp
    ring
  have hstep (t : ℝ) (ht : 0 < t) :
      M t * t ^ p ≤ (2 ^ p * (N * E ^ a)) * (M (t / 2) * (t / 2) ^ p) ^ b := by
    have ht₂ : 0 < t / 2 := by positivity
    have hn := hnash _ (htrunc _ ht₂)
      (fun x => (levelTruncation_bounds u ht₂.le x).1)
    have hlower := sq_mul_measure_le_integral_levelTruncation_sq (μ := μ) hu ht₂.le
    have hupper := integral_levelTruncation_le (μ := μ) hu ht₂.le
    have he := henergy _ ht₂
    have hn' : (t / 2) ^ 2 * M (2 * (t / 2)) ≤
        (N * E ^ a) * ((t / 2) * M (t / 2)) ^ b := by
      apply hlower.trans (hn.trans _)
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow he.1 he.2 ha) hN
      · exact Real.rpow_le_rpow
          (integral_nonneg (fun x => (levelTruncation_bounds u ht₂.le x).1)) hupper hb
      · exact Real.rpow_nonneg
          (integral_nonneg (fun x => (levelTruncation_bounds u ht₂.le x).1)) _
      · exact mul_nonneg hN (Real.rpow_nonneg hE _)
    have hh := normalized_tail_step_of_truncated_nash ht₂
      (measureReal_nonneg (μ := μ)) hhom hn'
    simpa only [show 2 * (t / 2) = t by ring] using hh
  exact tail_le_of_normalized_recursion (M := M) (p := p)
    (fun _ _ => measureReal_nonneg (μ := μ)) (measureReal_nonneg (μ := μ) (s := univ))
    (fun _ _ => measureReal_mono (subset_univ _))
    (mul_nonneg (Real.rpow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) _) (mul_nonneg hN (Real.rpow_nonneg hE _)))
    hb hb₁ hp hs hstep

end HeatKernel.Sobolev
