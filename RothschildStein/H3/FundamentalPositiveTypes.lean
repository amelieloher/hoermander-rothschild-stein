-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.PositiveType
public import RothschildStein.H1.KernelData

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3

/-- the actual fundamental kernel has positive type two. -/
theorem fundamental_type_two {n q : ℕ} (G : HomogeneousGroup n)
    (H : H1.StandingHypotheses G q) (K : H1.FundamentalKernel G H) :
    PositiveType G 2 K := ⟨by norm_num, K.smooth_off_zero, K.homogeneous⟩

/-- each actual horizontal first kernel derivative has
positive type one, from the proved weighted word homogeneity. -/
theorem fundamental_horizontal_type_one {n q : ℕ} (G : HomogeneousGroup n)
    (H : H1.StandingHypotheses G q) (K : H1.FundamentalKernel G H) (i : Fin q) :
    PositiveType G 1 (fieldDerivative (H.fields i.succ) K) := by
  refine ⟨by norm_num, ?_, ?_⟩
  · simpa only [wordDerivative] using H.wordDerivative_smooth_off_zero G K.smooth_off_zero [i.succ]
  · have hh := H.wordDerivative_homogeneous G K.smooth_off_zero K.homogeneous [i.succ]
    have hw : H1.differentialWordWeight [i.succ] = 1 := by simp [H1.differentialWordWeight]
    rw [hw] at hh
    have he : 2-(G.homogeneousDimension : ℝ)-(1 : ℕ) = 1-(G.homogeneousDimension : ℝ) := by ring
    simpa only [wordDerivative, he] using hh

end RothschildStein.H3
