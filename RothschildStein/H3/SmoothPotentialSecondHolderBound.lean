-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.FundamentalSecondHolder
public import RothschildStein.H3.SecondJetPrincipalValueHolderBound
public import RothschildStein.H3.SecondJetHolderConstant
public import RothschildStein.H3.SmoothSourceFrozenHolder

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped ENNReal NNReal BigOperators
namespace RothschildStein.H3

/-- Actual PV Hölder bounds control all horizontal second
potential jets and the drift jet of every smooth compact source. The
coefficient is fixed before the source; no PV estimate is assumed. -/
theorem smooth_potential_second_holder_bound_of_controlNorm {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H) (hQ : 2 < (G.homogeneousDimension : ℝ))
    (C : G2.ControlNormConclusion G driftWeight H.fields)
    {a : ℝ≥0} (ha : 0 < a) (ha1 : (a : ℝ) < 1)
    (V : Opens (Fin N → ℝ)) {R : ℝ} (hR : 0 < R)
    (hVR : ∀ x ∈ V, C.norm x < R) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ f : (Fin N → ℝ) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → tsupport f ⊆ (V : Set (Fin N → ℝ)) →
      (∑ i : Fin q, ∑ j : Fin q,
        holderENorm (controlDistance univ driftWeight H.fields) a (V : Set (Fin N → ℝ))
          (wordDerivative H.fields [i.succ, j.succ] (G2.groupConvolution G f K))) +
      holderENorm (controlDistance univ driftWeight H.fields) a (V : Set (Fin N → ℝ))
        (wordDerivative H.fields [0] (G2.groupConvolution G f K)) ≤
      ((q : ℝ≥0∞)^2 + (1 + (q : ℝ≥0∞))) * ENNReal.ofReal L *
        holderENorm (controlDistance univ driftWeight H.fields) a univ f := by
  classical
  let metric : MetricSpace (ControlCarrier N) :=
    gaugeMetric G C.norm C.constant_one C.symmetric
  obtain ⟨B, hB, hPV⟩ := exists_fundamental_second_PV_holder_bounds_of_controlNorm
    G H K C ha ha1 V hR hVR
  obtain ⟨c, _htype, hform⟩ := convolution_formulas_of_fundamental_kernel G
    (standingWithNorm G H C.norm) (fundamentalKernelWithNorm G H C.norm K) hQ
  let L := secondJetHolderMax B c
  have hL : 1 ≤ L := one_le_secondJetHolderMax B c
  refine ⟨L, hL, ?_⟩
  intro f hf hc hs
  have hsource := smooth_source_global_holder_finite_of_controlNorm G H.fields C a ha1.le
    R f hf hc (fun x hx => hVR x (hs hx))
  have haux : @H2.BoundedHolder (ControlCarrier N) metric a univ f := by
    rwa [frozen_holderENorm_eq_control_norm G driftWeight H.fields C] at hsource
  let v := G2.groupConvolution G f K
  let second := fun i j : Fin q => wordDerivative H.fields [i.succ, j.succ] v
  let drift := wordDerivative H.fields [0] v
  have hp := hform f hf hc
  have heq : f = fun x => drift x + ∑ i : Fin q, second i i x := hp.2.1.symm
  have hrep (i j : Fin q) : second i j = fun x => H1.principalValueConvolution G C.norm
      (fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields j.succ) K)) f x + c i j * f x :=
    hp.2.2.2.2.1 i j
  have hb := second_jet_holder_bound_of_principal_value_estimates G C.norm
    C.constant_one C.symmetric a (V : Set (Fin N → ℝ)) f drift second
    (fun i j => fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields j.succ) K))
    c B 1 L (by norm_num) hL hB (coefficient_le_secondJetHolderMax B c hB) heq hrep
    (hPV f hf.continuous hc hs haux)
  simp only [ENNReal.ofReal_one, one_mul] at hb
  simp only [frozen_holderENorm_eq_control_norm G driftWeight H.fields C]
  exact hb.trans (mul_le_mul' le_rfl
    (H2.boundedHolderNorm_restrict (subset_univ (V : Set (Fin N → ℝ)))))

end RothschildStein.H3
