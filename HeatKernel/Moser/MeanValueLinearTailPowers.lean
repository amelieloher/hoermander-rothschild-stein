-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueBoundedPowers
public import Mathlib.Analysis.Normed.MulAction
import Mathlib.Tactic

/-! # Positive-power tests with a linear upper tail -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology NNReal
namespace HeatKernel

/-- Extend the positive power beyond its upper threshold by a linear tail. -/
def linearTailPositivePower (M γ s : ℝ) : ℝ :=
  boundedPositivePower M γ s + M ^ (γ - 1) * max 0 (s - M)

/-- The linear-tail extension is globally Lipschitz with an explicit threshold bound. -/
theorem lipschitzWith_linearTailPositivePower {M γ : ℝ} (hM : 0 ≤ M) (hγ : 1 ≤ γ) :
    LipschitzWith (Real.toNNReal (γ * M ^ (γ - 1)) + ‖M ^ (γ - 1)‖₊)
      (linearTailPositivePower M γ) := by
  have ht₀ : LipschitzWith 1 (fun s : ℝ => s - M) := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    simp only [dist_sub_right, NNReal.coe_one, one_mul, le_refl]
  have ht := ht₀.const_max (0 : ℝ)
  have hs : LipschitzWith ‖M ^ (γ - 1)‖₊
      (fun s : ℝ => M ^ (γ - 1) * max 0 (s - M)) := by
    simpa only [mul_one, smul_eq_mul, Function.comp_def] using
      (lipschitzWith_smul (M ^ (γ - 1))).comp ht
  exact (lipschitzWith_boundedPositivePower hM hγ).add hs

/-- The linear-tail power fixes zero. -/
@[simp] theorem linearTailPositivePower_zero {M γ : ℝ} (hM : 0 ≤ M) (hγ : 0 < γ) :
    linearTailPositivePower M γ 0 = 0 := by
  simp only [linearTailPositivePower, boundedPositivePower_zero hM hγ,
    zero_sub, max_eq_left (neg_nonpos.mpr hM), mul_zero, add_zero]

/-- Below the upper threshold the test is the ordinary positive power. -/
theorem linearTailPositivePower_eq_rpow {M γ s : ℝ} (hs : 0 ≤ s) (hsM : s ≤ M) :
    linearTailPositivePower M γ s = s ^ γ := by
  simp only [linearTailPositivePower, boundedPositivePower_eq_rpow hs hsM,
    max_eq_left (sub_nonpos.mpr hsM), mul_zero, add_zero]

/-- Above a positive upper threshold the test has the exact linear continuation. -/
theorem linearTailPositivePower_eq_linear {M γ s : ℝ} (hM : 0 < M) (hs : M ≤ s) :
    linearTailPositivePower M γ s = M ^ (γ - 1) * s := by
  have hp : M ^ γ = M ^ (γ - 1) * M := by
    simpa only [sub_add_cancel, Real.rpow_one] using Real.rpow_add hM (γ - 1) 1
  simp only [linearTailPositivePower, boundedPositivePower,
    min_eq_left (hs.trans (le_max_right _ _)), max_eq_right (sub_nonneg.mpr hs), hp]
  ring

/-- The only possible corners of the test are zero and the upper threshold. -/
theorem contDiffAt_linearTailPositivePower {M γ s : ℝ} (hs0 : s ≠ 0) (hsM : s ≠ M) :
    ContDiffAt ℝ 1 (linearTailPositivePower M γ) s := by
  have ht : ContDiffAt ℝ 1 (fun t : ℝ => max 0 (t - M)) s := by
    rcases lt_or_gt_of_ne hsM with hs | hs
    · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [Iio_mem_nhds hs] with t ht
      exact max_eq_left (sub_nonpos.mpr ht.le)
    · apply (contDiffAt_id.sub contDiffAt_const).congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds hs] with t ht
      exact max_eq_right (sub_nonneg.mpr ht.le)
  exact (contDiffAt_boundedPositivePower hs0 hsM).add (contDiffAt_const.mul ht)

end HeatKernel
