-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.LocalLpRegularityControlNorm
public import RothschildStein.H3.SmoothNormFlowGeometry
public import RothschildStein.H3.InteriorEstimate
public import RothschildStein.H3.GaugePairComparison
public import RothschildStein.H3.LocalSobolevIntegrability
public import RothschildStein.H3.FrozenDriftEquationRestriction
public import RothschildStein.H3.WeakOperatorDistributionUniqueness

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal
namespace RothschildStein.H3

/-- Local regularity for distribution representatives, including the
ENNReal interior estimate under the stated geometric and global-flow
hypotheses (BB pp. 374–375). -/
theorem localLpRegularity_of_geometry_and_flow {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H) (hQ : 2 < (G.homogeneousDimension : ℝ))
    (P : G2.ControlNormConclusion G driftWeight H.fields)
    (E : Fin q → ℝ → (Fin N → ℝ))
    (hE : ∀ i, Continuous (E i)) (hE0 : ∀ i, E i 0 = 0)
    (hflow : ∀ i x, IsIntegralCurve (fun t => G.mul x (E i t)) (fun _ => H.fields i.succ)) :
    Provider.LocalLpRegularity G driftWeight H.fields
      (fun Ω T f => hasDistributionEquationWithDrift Ω H.fields
        (fun i => (H.fields_smooth G i).contDiffOn) T f) P.norm := by
  refine ⟨localLpRegularity_of_controlNorm G H K hQ P,?_⟩
  intro p hp hpt Ω A V hAK hAV hVK hVΩ
  have hpt' : p ≠ ⊤ := hpt.ne
  have hpReal : 1 < p.toReal := by
    simpa only [ENNReal.toReal_one] using
      (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hpt').2 hp
  obtain ⟨B,hB,hhalf⟩ := smoothNorm_estimate_of_geometry_flow G H K hQ P p hp.le hpt'
    hpReal E hE hE0 hflow
  obtain ⟨a,b,ha,hb,hcmp⟩ := exists_gauge_pair_comparison P.norm (G2.smoothNorm G)
  obtain ⟨c,hc,hbound⟩ := interior_estimate_of_controlNorm_and_halfRadius
    G (G2.smoothNorm G) H.fields P a b ha hb hcmp V A hAK hAV p hp.le B hB.le hhalf
  refine ⟨c,hc,?_⟩
  intro u f hu heq hf
  have huV := hu V hVK hVΩ
  have huA := hu A hAK (hAV.trans (subset_closure.trans hVΩ))
  have hUloc := locallyIntegrableOn_of_memSobolevXLoc driftWeight H.fields Ω 2 p hp.le hu
  have heqV := frozen_drift_equation_restrict Ω V (subset_closure.trans hVΩ)
    H.fields (fun i => (H.fields_smooth G i).contDiffOn) u f hUloc heq
  obtain ⟨D⟩ := exists_weakDriftOperatorData H.fields V p u huV
  have hforcing := D.operator_ae_eq_of_distribution_equation hp.le
    (fun i => (H.fields_smooth G i).contDiffOn) f heqV.1 (fun ψ => by
      rw [adjointTest_zero_eq_driftTransposeTest]
      exact heqV.2 ψ)
  have hestimate := hbound u huV D
  rw [eLpNorm_congr_ae hforcing] at hestimate
  have hfinite := (sobolevXENorm_lt_top_of_membership driftWeight H.fields A 2 p huA).ne
  calc
    _ = ENNReal.ofReal (sobolevXENorm driftWeight H.fields A 2 p u).toReal :=
      (ENNReal.ofReal_toReal hfinite).symm
    _ ≤ ENNReal.ofReal (c*((eLpNorm f p (volume.restrict (V : Set (Fin N → ℝ)))).toReal +
        (eLpNorm u p (volume.restrict (V : Set (Fin N → ℝ)))).toReal)) :=
      ENNReal.ofReal_le_ofReal hestimate
    _ = _ := by
      rw [ENNReal.ofReal_mul hc.le, ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal hf.eLpNorm_lt_top.ne, ENNReal.ofReal_toReal huV.1.eLpNorm_lt_top.ne]

end RothschildStein.H3
