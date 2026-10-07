-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.DriftCoefficient
public import RothschildStein.H1.BarrierEstimate
public import RothschildStein.H1.Liouville

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.H1
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- Liouville for every standing comparison operator and every
real drift coefficient (BB Thm 1.57, pp. 37–38). -/
theorem StandingHypotheses.liouville (H : StandingHypotheses G q) (a : ℝ)
    {f : (Fin N → ℝ) → ℝ} (hf : ContDiff ℝ 2 f)
    (hP : ∀ x, sumSquaresWithDrift (driftCoefficientFields G H a) f x = 0)
    (hdecay : ∀ ε > 0, ∃ R : ℝ, ∀ x, R ≤ ‖x‖ → ‖f x‖ ≤ ε) : f = 0 :=
  eq_zero_of_null_solution_decay_of_barrier (firstIndex G) (barrierRate G H)
    (driftCoefficientFields_barrier G H a) hf
    (fun i => (driftCoefficientFields_smooth G H a i.succ).differentiable (by simp)) hP hdecay

end RothschildStein.H1
