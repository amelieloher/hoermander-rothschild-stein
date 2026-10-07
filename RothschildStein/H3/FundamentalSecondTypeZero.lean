-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.TypeZeroPrincipalValue
public import RothschildStein.H1.FundamentalSecondDerivative
public import RothschildStein.H1.WordBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory

/-- The actual second derivatives of the homogeneous fundamental kernel
lie in the fixed-gauge type-zero class, without a separate kernel-class
assumption. -/
theorem fundamental_second_typeZero {n q : ℕ}
    (G : HomogeneousGroup n) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H) (i j : Fin q) :
    TypeZero G H.norm (fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields j.succ) K)) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [wordDerivative] using
      H.wordDerivative_smooth_off_zero G K.smooth_off_zero [i.succ,j.succ]
  · have hh := H.wordDerivative_homogeneous G K.smooth_off_zero K.homogeneous [i.succ,j.succ]
    have hw : H1.differentialWordWeight [i.succ,j.succ] = 2 := by
      simp [H1.differentialWordWeight]
    rw [hw] at hh
    have he : 2-(G.homogeneousDimension : ℝ)-(2 : ℕ) = -(G.homogeneousDimension : ℝ) := by ring
    simpa only [wordDerivative, he] using hh
  · exact K.secondDerivative_shellCancellation G H i j 1 (Real.exp 1) zero_lt_one
      (Real.one_lt_exp_iff.mpr zero_lt_one)

end RothschildStein.H3
