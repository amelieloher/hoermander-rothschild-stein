-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-! # Bounded positive-power compositions for mean-value iteration -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology NNReal
namespace HeatKernel

/-- A positive power with its argument clipped to a bounded nonnegative interval. -/
def boundedPositivePower (M γ s : ℝ) : ℝ := (min M (max 0 s)) ^ γ

/-- Positive powers of exponent at least one have a uniform derivative bound on a bounded range. -/
theorem lipschitzOnWith_rpow_Icc {M γ : ℝ} (hM : 0 ≤ M) (hγ : 1 ≤ γ) :
    LipschitzOnWith (Real.toNNReal (γ * M ^ (γ - 1)))
      (fun s : ℝ => s ^ γ) (Icc 0 M) := by
  apply (convex_Icc 0 M).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (f' := fun s => γ * s ^ (γ - 1))
  · intro s _
    exact (Real.hasDerivAt_rpow_const (Or.inr hγ)).hasDerivWithinAt
  · intro s hs
    have hp := Real.rpow_le_rpow hs.1 hs.2 (sub_nonneg.mpr hγ)
    have hn : ‖γ * s ^ (γ - 1)‖ ≤ γ * M ^ (γ - 1) := by
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (zero_le_one.trans hγ),
        Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hs.1 _)]
      exact mul_le_mul_of_nonneg_left hp (zero_le_one.trans hγ)
    have he : ‖γ * s ^ (γ - 1)‖ ≤ (Real.toNNReal (γ * M ^ (γ - 1)) : ℝ) := by
      simpa only [Real.coe_toNNReal _
        (mul_nonneg (zero_le_one.trans hγ) (Real.rpow_nonneg hM _))] using hn
    exact_mod_cast he

/-- Clipping makes the positive-power composition globally Lipschitz. -/
theorem lipschitzWith_boundedPositivePower {M γ : ℝ} (hM : 0 ≤ M) (hγ : 1 ≤ γ) :
    LipschitzWith (Real.toNNReal (γ * M ^ (γ - 1))) (boundedPositivePower M γ) := by
  have hc := (LipschitzWith.id.const_max (0 : ℝ)).const_min M
  have hr (s : ℝ) : min M (max 0 s) ∈ Icc 0 M :=
    ⟨le_min hM (le_max_left _ _), min_le_left _ _⟩
  apply LipschitzWith.of_dist_le_mul
  intro s t
  exact ((lipschitzOnWith_rpow_Icc hM hγ).dist_le_mul _ (hr s) _ (hr t)).trans
    (mul_le_mul_of_nonneg_left (by simpa using hc.dist_le_mul s t)
      (Real.toNNReal _).coe_nonneg)

/-- The bounded power fixes zero, as required for global energy compositions. -/
@[simp] theorem boundedPositivePower_zero {M γ : ℝ} (hM : 0 ≤ M) (hγ : 0 < γ) :
    boundedPositivePower M γ 0 = 0 := by
  simp only [boundedPositivePower, max_self, min_eq_right hM, Real.zero_rpow hγ.ne']

/-- On the untruncated nonnegative range the bounded power is the ordinary power. -/
theorem boundedPositivePower_eq_rpow {M γ s : ℝ} (hs : 0 ≤ s) (hsM : s ≤ M) :
    boundedPositivePower M γ s = s ^ γ := by
  simp only [boundedPositivePower, max_eq_right hs, min_eq_right hsM]

/-- The only possible corners of the bounded power are its two clipping thresholds. -/
theorem contDiffAt_boundedPositivePower {M γ s : ℝ}
    (hs0 : s ≠ 0) (hsM : s ≠ M) :
    ContDiffAt ℝ 1 (boundedPositivePower M γ) s := by
  rcases lt_or_gt_of_ne hsM with hsM | hMs
  · rcases lt_or_gt_of_ne hs0 with hs0 | h0s
    · apply (contDiffAt_const (c := (min M 0) ^ γ)).congr_of_eventuallyEq
      filter_upwards [Iio_mem_nhds hs0] with t ht
      simp only [boundedPositivePower, max_eq_left ht.le]
    · apply (Real.contDiffAt_rpow_const_of_ne (p := γ) h0s.ne').congr_of_eventuallyEq
      filter_upwards [Ioo_mem_nhds h0s hsM] with t ht
      simp only [boundedPositivePower, max_eq_right ht.1.le, min_eq_right ht.2.le]
  · apply (contDiffAt_const (c := M ^ γ)).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hMs] with t ht
    simp only [boundedPositivePower, min_eq_left (ht.le.trans (le_max_right _ _))]

end HeatKernel
