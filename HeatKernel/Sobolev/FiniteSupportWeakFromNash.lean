-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.WeakFromNash
import Mathlib.Tactic

/-! # Weak distribution estimates on finite-volume supports -/

@[expose] public section
open Set MeasureTheory
open scoped ENNReal
namespace HeatKernel.Sobolev

/-- Truncated Nash estimates on a finite-volume support give a weak tail on the ambient space. -/
theorem measure_abs_gt_le_of_supported_truncated_nash
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {B : Set α}
    {u : α → ℝ} (hu : Measurable u) (hsupport : Function.support u ⊆ B)
    (hfinite : μ B ≠ ⊤) {H b : ℝ} (hH : 0 ≤ H) (hb : 0 ≤ b) (hb₁ : b < 1)
    (hnash : ∀ t : ℝ, 0 < t →
      (∫ x, levelTruncation u t x ^ 2 ∂μ) ≤
        H * (∫ x, levelTruncation u t x ∂μ) ^ b)
    {s : ℝ} (hs : 0 < s) :
    μ.real {x | s < |u x|} ≤
      (2 ^ ((2 - b) / (1 - b)) * H) ^ (1 / (1 - b)) *
        s ^ (-((2 - b) / (1 - b))) := by
  let _ : IsFiniteMeasure (μ.restrict B) := ⟨by
    simpa only [Measure.restrict_apply_univ] using hfinite.lt_top⟩
  have hzero (x : α) (hx : x ∉ B) : u x = 0 := by
    by_contra hne
    exact hx (hsupport hne)
  have htrunczero (t : ℝ) (ht : 0 < t) (x : α) (hx : x ∉ B) :
      levelTruncation u t x = 0 :=
    levelTruncation_eq_zero u ht.le (by rw [hzero x hx, abs_zero]; exact ht.le)
  have hI₁ (t : ℝ) (ht : 0 < t) :
      (∫ x, levelTruncation u t x ∂μ.restrict B) = ∫ x, levelTruncation u t x ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (htrunczero t ht)
  have hI₂ (t : ℝ) (ht : 0 < t) :
      (∫ x, levelTruncation u t x ^ 2 ∂μ.restrict B) = ∫ x, levelTruncation u t x ^ 2 ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by rw [htrunczero t ht x hx]; norm_num)
  have hlocal : ∀ f ∈ {f : α → ℝ | ∃ t : ℝ, 0 < t ∧ f = levelTruncation u t},
      (∀ x, 0 ≤ f x) → (∫ x, f x ^ 2 ∂μ.restrict B) ≤
        H * (1 : ℝ) ^ (0 : ℝ) * (∫ x, f x ∂μ.restrict B) ^ b := by
    rintro f ⟨t, ht, rfl⟩ _
    simpa only [hI₁ t ht, hI₂ t ht, Real.rpow_zero, mul_one] using hnash t ht
  have Htail := measure_abs_gt_le_of_nash_truncation (μ := μ.restrict B)
    (D := {f : α → ℝ | ∃ t : ℝ, 0 < t ∧ f = levelTruncation u t})
    (energy := fun _ => (1 : ℝ)) (E := 1) (a := 0)
    hu hH (by norm_num) (by norm_num) hb hb₁ hlocal
    (fun t ht => ⟨t, ht, rfl⟩) (fun _ _ => ⟨by norm_num, le_rfl⟩) hs
  have hsub : {x | s < |u x|} ⊆ B := by
    intro x hx
    by_contra hn
    change s < |u x| at hx
    rw [hzero x hn, abs_zero] at hx
    linarith
  have heq : (μ.restrict B).real {x | s < |u x|} = μ.real {x | s < |u x|} := by
    change ((μ.restrict B) {x | s < |u x|}).toReal = _
    rw [Measure.restrict_apply (by measurability), inter_eq_left.mpr hsub]
    rfl
  simpa only [heq, Real.one_rpow, mul_one] using Htail

end HeatKernel.Sobolev
