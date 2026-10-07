-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.FundamentalSecondCenteredHolder

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped ENNReal NNReal
namespace RothschildStein.H3

/-- The same center-uniform PV constants work on every open
subdomain of the fixed-radius ball when the source is compact there. -/
theorem exists_fundamental_second_local_PV_holder_bounds_of_controlNorm {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H)
    (C : G2.ControlNormConclusion G driftWeight H.fields)
    {a : ℝ≥0} (ha : 0 < a) (ha1 : (a : ℝ) < 1)
    {R : ℝ} (hR : 0 < R) :
    let metric : MetricSpace (ControlCarrier N) :=
      gaugeMetric G C.norm C.constant_one C.symmetric
    ∃ B : Fin q → Fin q → ℝ, (∀ i j, 0 ≤ B i j) ∧
      ∀ z : Fin N → ℝ, ∀ U : Opens (Fin N → ℝ),
        (U : Set (Fin N → ℝ)) ⊆ quasiballDomain G C.norm z R →
        ∀ F : ControlCarrier N → ℝ, Continuous F → HasCompactSupport F →
        tsupport F ⊆ (U : Set (Fin N → ℝ)) →
        @H2.BoundedHolder (ControlCarrier N) metric a univ F → ∀ i j,
          @H2.boundedHolderNorm (ControlCarrier N) metric a (U : Set (Fin N → ℝ))
            (H1.principalValueConvolution G C.norm
              (fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields j.succ) K)) F) ≤
          ENNReal.ofReal (B i j) *
            @H2.boundedHolderNorm (ControlCarrier N) metric a (U : Set (Fin N → ℝ)) F := by
  let metric : MetricSpace (ControlCarrier N) :=
    gaugeMetric G C.norm C.constant_one C.symmetric
  dsimp only
  obtain ⟨B, hB, hb⟩ := exists_fundamental_second_centered_PV_holder_bounds_of_controlNorm
    G H K C ha ha1 hR
  refine ⟨B, hB, ?_⟩
  intro z U hU F hF hc hs hf i j
  have hf' : holderENorm (controlDistance univ driftWeight H.fields) a univ F < ⊤ := by
    rw [frozen_holderENorm_eq_control_norm G driftWeight H.fields C]
    exact hf
  have he := hb z F hF hc (hs.trans hU) hf' i j
  rw [frozen_holderENorm_eq_control_norm G driftWeight H.fields C,
    frozen_holderENorm_eq_control_norm G driftWeight H.fields C] at he
  have hext : @H2.boundedHolderNorm (ControlCarrier N) metric a univ F =
      @H2.boundedHolderNorm (ControlCarrier N) metric a (U : Set (Fin N → ℝ)) F :=
    boundedHolderNorm_global_eq_of_controlNorm (a := a) C U.isOpen hc hs
  have hsource : @H2.boundedHolderNorm (ControlCarrier N) metric a
      (quasiballDomain G C.norm z R : Set (Fin N → ℝ)) F ≤
      @H2.boundedHolderNorm (ControlCarrier N) metric a (U : Set (Fin N → ℝ)) F := by
    rw [← hext]
    exact H2.boundedHolderNorm_restrict (subset_univ _)
  have hout : @H2.boundedHolderNorm (ControlCarrier N) metric a (U : Set (Fin N → ℝ))
      (H1.principalValueConvolution G C.norm
        (fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields j.succ) K)) F) ≤
      @H2.boundedHolderNorm (ControlCarrier N) metric a
        (quasiballDomain G C.norm z R : Set (Fin N → ℝ))
        (H1.principalValueConvolution G C.norm
          (fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields j.succ) K)) F) :=
    H2.boundedHolderNorm_restrict hU
  exact hout.trans (he.trans (mul_le_mul' le_rfl hsource))

end RothschildStein.H3
