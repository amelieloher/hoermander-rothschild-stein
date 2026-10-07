-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.CanonicalDensityRemainder
public import RothschildStein.L1.AbsoluteJacobianNegation
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
namespace RothschildStein.L1
namespace CanonicalFrameChartData
variable {N : ℕ} {Ω : Set (Fin N → ℝ)}
variable {Y : Fin N → (Fin N → ℝ) → (Fin N → ℝ)} {x : Fin N → ℝ}

/-- The actual Lebesgue Jacobian of the first-variable inverse map. -/
def firstVariableDensity (C : CanonicalFrameChartData Ω Y x)
    (q : (Fin N → ℝ) × (Fin N → ℝ)) : ℝ :=
  |(fderiv ℝ (fun u => canonicalFrameMap C.time C.flow (q.1,-u)) q.2).det|

/-- The first-variable density is precisely
the forward density at negated coordinates, including the unit absolute
Jacobian of the coordinate sign change. -/
theorem firstVariableDensity_eq (C : CanonicalFrameChartData Ω Y x)
    (q : (Fin N → ℝ) × (Fin N → ℝ))
    (hq : q ∈ ball x C.radius ×ˢ ball 0 C.radius) :
    C.firstVariableDensity q = C.forwardDensity (q.1,-q.2) := by
  have hnu : -q.2 ∈ ball 0 C.radius := by
    simpa only [mem_ball_zero_iff,norm_neg] using hq.2
  have hj : ContDiffAt ℝ (⊤ : ℕ∞) (canonicalFrameMap C.time C.flow) (q.1,-q.2) :=
    C.forward_smooth.contDiffAt ((isOpen_ball.prod isOpen_ball).mem_nhds ⟨hq.1,hnu⟩)
  have ha : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun u : Fin N → ℝ => (q.1,u)) (-q.2) :=
    contDiffAt_const.prodMk contDiffAt_id
  have hf := hj.comp (-q.2) (f := fun u => (q.1,u)) ha
  exact abs_fderiv_precompose_neg (fun u => canonicalFrameMap C.time C.flow (q.1,u))
    q.2 (hf.differentiableAt (by simp))

end CanonicalFrameChartData
end RothschildStein.L1
