-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Tactic.Ring

/-! Constant-difference estimates on a common subset of two averaging domains. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace HeatKernel

/-- The difference of two constants, measured on their common subset, is bounded by
the two oscillation seminorms on the larger domains. No minimization property is used. -/
theorem ofReal_abs_sub_mul_measure_rpow_le_eLpNorms {E : Type*} [MeasurableSpace E]
    (μ : Measure E) (f : E → ℝ) (c d : ℝ) {A U V : Set E}
    (hAU : A ⊆ U) (hAV : A ⊆ V) {p : ℝ≥0∞} (hp : 1 ≤ p) (hptop : p ≠ ⊤) :
    ENNReal.ofReal |c - d| * μ A ^ (1 / p.toReal) ≤
      eLpNorm (fun x => f x - c) p (μ.restrict U) +
        eLpNorm (fun x => f x - d) p (μ.restrict V) := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 1) hp).ne'
  have heq : (fun x => f x - c) - (fun x => f x - d) = (fun _ => d - c) := by
    funext x
    simp only [Pi.sub_apply]
    ring
  have ht := eLpNorm_sub_le (μ := μ.restrict A)
    (f := fun x => f x - c) (g := fun x => f x - d) hp
  rw [heq, eLpNorm_const' (d - c) hp0 hptop, Measure.restrict_apply_univ,
    Real.enorm_eq_ofReal_abs, abs_sub_comm d] at ht
  exact ht.trans (add_le_add
    (eLpNorm_mono_measure _ (Measure.restrict_mono hAU le_rfl))
    (eLpNorm_mono_measure _ (Measure.restrict_mono hAV le_rfl)))

end HeatKernel
