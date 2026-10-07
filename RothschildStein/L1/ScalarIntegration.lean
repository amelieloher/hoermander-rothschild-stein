-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Filter

namespace RothschildStein.L1

/-- One vertical coordinate is obtained on the entire interval
by integrating its already determined measurable, integrable right side. -/
theorem exists_scalar_ac_primitive {f : ℝ → ℝ} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) (z : ℝ) :
    ∃ v : ℝ → ℝ, AbsolutelyContinuousOnInterval v a b ∧ v a = z ∧
      ∀ᵐ t ∂volume, t ∈ uIcc a b → HasDerivAt v (f t) t := by
  let v : ℝ → ℝ := fun t => z + ∫ q in a..t, f q
  refine ⟨v, ?_, ?_, ?_⟩
  · have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => z) a b := by
      simpa only [AbsolutelyContinuousOnInterval, dist_self, Finset.sum_const_zero] using
        (tendsto_const_nhds : Tendsto (fun _ => (0 : ℝ)) _ (nhds 0))
    exact hc.add (hf.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc)
  · simp [v]
  · filter_upwards [hf.ae_hasDerivAt_integral] with t ht
    intro hmem
    convert! (hasDerivAt_const t z).add (ht hmem a left_mem_uIcc) using 1
    simp

end RothschildStein.L1
