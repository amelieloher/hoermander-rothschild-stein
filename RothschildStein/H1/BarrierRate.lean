-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.Barriers

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

@[expose] public section
noncomputable section
namespace RothschildStein.H1
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- The positive normalization rate γ₀=c₀^(-1/2) (BB p. 257). -/
def barrierRate (H : StandingHypotheses G q) : ℝ :=
  (Real.sqrt (horizontalFirstSquareSum G H))⁻¹

/-- The normalization rate is strictly positive (BB p. 257). -/
theorem barrierRate_pos (H : StandingHypotheses G q) : 0 < barrierRate G H :=
  inv_pos.mpr (Real.sqrt_pos.mpr (H.horizontalFirstSquareSum_pos G))

/-- The named normalized barrier satisfies L(exp(γ₀x₁))=exp(γ₀x₁) (BB p. 257). -/
theorem StandingHypotheses.operator_barrier (H : StandingHypotheses G q) (x : Fin N → ℝ) :
    sumSquaresWithDrift H.fields (fun y => Real.exp (barrierRate G H * y (firstIndex G))) x =
      Real.exp (barrierRate G H * x (firstIndex G)) := H.operator_normalized_exp G x

end RothschildStein.H1
