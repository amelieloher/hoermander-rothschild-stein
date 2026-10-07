-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.StandingControlNorm
public import RothschildStein.G2.StandingGlobalFlows
public import RothschildStein.H3.GlobalLpRegularityGeometry
public import RothschildStein.H3.LocalLpRegularityGeometry
public import RothschildStein.H3.BallLpSolvabilityGeometry
public import RothschildStein.H3.CompactHolderEstimatesGeometry

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3

/-- The shared global Lp regularity input with every geometry and flow
premise constructed from the standing hypotheses. -/
theorem globalLpRegularity_standing {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H) (hQ : 2 < (G.homogeneousDimension : ℝ))
    (νs : (Fin N → ℝ) → ℝ) :
    Provider.GlobalLpRegularity G driftWeight H.fields
      (fun Ω T f => hasDistributionEquationWithDrift Ω H.fields
        (fun i => (H.fields_smooth G i).contDiffOn) T f) νs := by
  obtain ⟨E, hE, hE0, hflow⟩ := H.exists_global_horizontal_flows G
  exact globalLpRegularity_of_geometry_and_flow G H K hQ
    (standingControlNormConclusion G H) E hE hE0 hflow

/-- The shared arbitrary-distribution local Sobolev
input, including its full interior norm, without extra certificates. -/
theorem localLpRegularity_standing {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H) (hQ : 2 < (G.homogeneousDimension : ℝ))
    (νs : (Fin N → ℝ) → ℝ) :
    Provider.LocalLpRegularity G driftWeight H.fields
      (fun Ω T f => hasDistributionEquationWithDrift Ω H.fields
        (fun i => (H.fields_smooth G i).contDiffOn) T f) νs := by
  obtain ⟨E, hE, hE0, hflow⟩ := H.exists_global_horizontal_flows G
  exact localLpRegularity_of_geometry_and_flow G H K hQ
    (standingControlNormConclusion G H) E hE hE0 hflow

/-- The exact bounded-domain Lp solver with the standing
control norm constructed internally. -/
theorem ballLpSolvability_standing {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H) (hQ : 2 < (G.homogeneousDimension : ℝ))
    (νs : (Fin N → ℝ) → ℝ) :
    Provider.BallLpSolvability G driftWeight H.fields
      (fun Ω T f => hasDistributionEquationWithDrift Ω H.fields
        (fun i => (H.fields_smooth G i).contDiffOn) T f) νs :=
  ballLpSolvability_of_controlNorm G H K hQ (standingControlNormConclusion G H)

/-- Both exact compact Holder estimates with the standing
control norm constructed internally. -/
theorem compactHolderEstimates_standing {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H) (hQ : 2 < (G.homogeneousDimension : ℝ))
    (νs : (Fin N → ℝ) → ℝ) :
    Provider.CompactHolderEstimates G driftWeight H.fields
      (fun Ω T f => hasDistributionEquationWithDrift Ω H.fields
        (fun i => (H.fields_smooth G i).contDiffOn) T f) νs :=
  compactHolderEstimates_of_controlNorm G H K hQ (standingControlNormConclusion G H)

end RothschildStein.H3
