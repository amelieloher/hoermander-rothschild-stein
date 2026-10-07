-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.LayerCake

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set MeasureTheory
open scoped ENNReal NNReal

namespace RothschildStein.H2

variable {Y : Type*} [MeasurableSpace Y]

/-- Large-value truncation at a real threshold (BB Thm 7.48, p. 334). -/
def highPart (f : Y → ℝ) (t : ℝ) : Y → ℝ :=
  {y | t < |f y|}.indicator f

/-- Small-value truncation at a real threshold (BB Thm 7.48, p. 334). -/
def lowPart (f : Y → ℝ) (t : ℝ) : Y → ℝ :=
  {y | |f y| ≤ t}.indicator f

omit [MeasurableSpace Y] in
/-- The two truncations sum to the original function
(BB Thm 7.48, p. 334). -/
theorem highPart_add_lowPart (f : Y → ℝ) (t : ℝ) :
    highPart f t + lowPart f t = f := by
  funext y
  by_cases h : t < |f y| <;> simp [highPart, lowPart, h, not_lt.mp, not_le.mpr]

/-- Joint measurability gives measurable truncation moments as functions
of the threshold (BB Thm 7.48, p. 334). -/
theorem measurable_moment_highPart (ν : Measure Y) [SFinite ν] {f : Y → ℝ}
    (hf : Measurable f) (q : ℝ) : Measurable (fun t => moment ν q (highPart f t)) := by
  have hj : Measurable (fun z : ℝ × Y => if z.1 < |f z.2| then f z.2 else 0) := by
    apply Measurable.ite (measurableSet_lt measurable_fst
      (by simpa only [Real.norm_eq_abs, Function.comp_apply] using (hf.comp measurable_snd).norm))
    · exact hf.comp measurable_snd
    · exact measurable_const
  apply Measurable.lintegral_prod_right
  simpa only [moment, highPart, indicator_apply, Real.norm_eq_abs, Function.uncurry_def, mem_ofPred_eq] using
    (hj.norm.pow_const q).ennreal_ofReal

end RothschildStein.H2
