-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.SmoothNormFlowGeometry
public import RothschildStein.G2.StandingGlobalFlows
public import RothschildStein.H3.StandingControlNorm

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace RothschildStein.H3

/-- For each prescribed smooth gauge, the half-radius Lp estimate follows
from the compact estimate, global-flow bounds, and density hypotheses
(BB pp. 374–375). -/
theorem halfRadius_estimate_prescribed_gauge {N q : ℕ} (G : HomogeneousGroup N)
    (H : H1.StandingHypotheses G q) (K : H1.FundamentalKernel G H)
    (hQ : 2 < (G.homogeneousDimension : ℝ))
    (ν : G2.HomogeneousNorm G) (hν : ν.Smooth)
    (p : ℝ≥0∞) (hp : 1 < p) (hpt : p < ⊤) :
    ∃ A : ℝ, 0 < A ∧ HalfRadiusEstimate G ν H.fields p A := by
  let hpFact : Fact (1 ≤ p) := ⟨hp.le⟩
  have hpReal : 1 < p.toReal := by
    simpa only [ENNReal.toReal_one] using
      (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hpt.ne).2 hp
  obtain ⟨A, hA, hb⟩ := compact_weight_two_estimate_of_fundamental_kernel_and_controlNorm G H K hQ
    (standingControlNormConclusion G H) hpReal
  obtain ⟨E, hE, hE0, hflow⟩ := H.exists_global_horizontal_flows G
  apply halfRadius_estimate_of_compact_flow_and_density G H ν hν p hp.le hpt.ne A hA.le
    (by simpa only [ENNReal.ofReal_toReal hpt.ne] using hb) E hE hE0 hflow
  intro v hv
  exact exists_sobolevWordApproximation_global_ennreal G H hpt.ne hpReal.le hv

end RothschildStein.H3
