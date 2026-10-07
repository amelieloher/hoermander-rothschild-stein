-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.StandingControlNorm
public import RothschildStein.G2.StandingGlobalFlows
public import RothschildStein.H3.SmoothNormFlowGeometry
public import RothschildStein.H3.HalfRadiusFrozenENNReal
public import RothschildStein.H3.FrozenDriftEquationBridge
public import RothschildStein.Provider.GroupRegularityInputs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal BigOperators
namespace RothschildStein.H3

/-- The scale-invariant estimate on a prescribed smooth gauge follows
from the half-radius estimate for arbitrary homogeneous norms. Under the
stated geometry, flow, and density hypotheses, the bound uses the specified
weighted sums. -/
theorem quasiballLpTransfer_standing {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H) (hQ : 2 < (G.homogeneousDimension : ℝ))
    (νs : (Fin N → ℝ) → ℝ) (hνs : G.IsHomogeneousGauge νs)
    (hνs_smooth : ContDiffOn ℝ (⊤ : ℕ∞) νs ({0}ᶜ)) :
    Provider.QuasiballLpTransfer G driftWeight H.fields
      (fun Ω T f => hasDistributionEquationWithDrift Ω H.fields
        (fun i => (H.fields_smooth G i).contDiffOn) T f) νs := by
  let P := standingControlNormConclusion G H
  let ν := G2.normOfGauge νs hνs
  have hν : ν.Smooth := hνs_smooth
  obtain ⟨E, hE, hE0, hflow⟩ := H.exists_global_horizontal_flows G
  intro p hp hpt
  have hpReal : 1 < p.toReal := by
    simpa only [ENNReal.toReal_one] using
      (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hpt.ne).mpr hp
  let hpFact : Fact (1 ≤ p) := ⟨hp.le⟩
  obtain ⟨A, hA, hb⟩ := compact_weight_two_estimate_of_fundamental_kernel_and_controlNorm G H K hQ P hpReal
  have hcompact : ∀ v : (Fin N → ℝ) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) v → HasCompactSupport v →
      ∀ I : List (Fin (q + 1)), wordWeight driftWeight I = 2 →
        eLpNorm (wordDerivative H.fields I v) p volume ≤
          ENNReal.ofReal A * eLpNorm (sumSquaresWithDrift H.fields v) p volume := by
    simpa only [ENNReal.ofReal_toReal hpt.ne] using hb
  have hdensity : ∀ v, memSobolevX driftWeight H.fields ⊤ 2 p v →
      Nonempty (SobolevWordApproximation driftWeight H.fields p v) :=
    fun v hv => exists_sobolevWordApproximation_global_ennreal G H hpt.ne hpReal.le hv
  obtain ⟨B, hB, hest⟩ := halfRadius_estimate_of_compact_flow_and_density
    G H ν hν p hp.le hpt.ne A hA.le hcompact E hE hE0 hflow hdensity
  refine ⟨B, hB, ?_⟩
  intro z r hr U V hU hV u hu
  have heU : U = quasiballDomain G ν z r := by ext x; exact hU x
  have heV : V = quasiballDomain G ν z (r / 2) := by ext x; exact hV x
  subst U
  subst V
  obtain ⟨D⟩ := exists_weakDriftOperatorData H.fields _ p u hu
  refine ⟨D.operator, D.operator_memLp, ?_,
    halfRadius_frozen_ennreal_estimate G ν H.fields p hB.le hest z hr u hu D⟩
  refine ⟨locallyIntegrableOn_of_locallyIntegrable_restrict
    (D.operator_memLp.locallyIntegrable hp.le), ?_⟩
  intro φ
  rw [frozen_drift_transpose_test_eq]
  have hh := D.ofFun_adjoint_equation hp.le (fun i => (H.fields_smooth G i).contDiffOn)
    D.operator Filter.EventuallyEq.rfl φ
  rw [adjointTest_zero_eq_driftTransposeTest] at hh
  exact hh

end RothschildStein.H3
