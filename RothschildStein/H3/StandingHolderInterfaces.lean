-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.StandingControlNorm
public import RothschildStein.H3.LocalHolderRegularityControlNorm
public import RothschildStein.H3.HolderBallTransferControlNorm
public import RothschildStein.G2.MollifierExistence
public import RothschildStein.G2.NormConstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3

/-- The exact local Holder regularity and estimate interface
for a standing homogeneous frame. Geometry and mollifiers are built;
only the actual fundamental kernel is supplied as upstream data. -/
theorem localHolderRegularity_standing {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H) (hQ : 2 < (G.homogeneousDimension : ℝ))
    (νs : (Fin N → ℝ) → ℝ) :
    Provider.LocalHolderRegularity G driftWeight H.fields
      (fun Ω T f => hasDistributionEquationWithDrift Ω H.fields
        (fun i => (H.fields_smooth G i).contDiffOn) T f) νs := by
  let C := standingControlNormConclusion G H
  let μ := Classical.choice (G2.nonempty_groupMollifier G H.norm)
  let φ := Classical.choice (G2.nonempty_groupMollifier G C.norm)
  exact localHolderRegularity_of_controlNorm G H K hQ C μ φ νs

/-- The exact enlarged gauge
ball solver interface for a standing frame and any prescribed fixed
gauge. Its norm certificate and mollifier are constructed internally. -/
theorem holderBallTransfer_standing {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H) (hQ : 2 < (G.homogeneousDimension : ℝ))
    (νs : (Fin N → ℝ) → ℝ) (hνs : G.IsHomogeneousGauge νs) :
    Provider.HolderBallTransfer G driftWeight H.fields
      (fun Ω T f => hasDistributionEquationWithDrift Ω H.fields
        (fun i => (H.fields_smooth G i).contDiffOn) T f) νs := by
  let C := standingControlNormConclusion G H
  let φ := Classical.choice (G2.nonempty_groupMollifier G C.norm)
  exact holderBallTransfer_of_controlNorm G H K hQ C φ (G2.normOfGauge νs hνs)

end RothschildStein.H3
