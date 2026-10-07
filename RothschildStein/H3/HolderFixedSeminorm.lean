-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.HolderGlobalSeminorm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped BigOperators ENNReal NNReal
namespace RothschildStein.H3

/-- The compact intrinsic input satisfies the global seminorm estimate
with the unit-ball constant under the global control-norm comparison and
unit principal-value bounds (BB Corollary 8.51, p. 380). -/
theorem seminorm_estimate_of_unit_principal_value_bounds {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H) (hQ : 2 < (G.homogeneousDimension : ℝ))
    (C : G2.ControlNormConclusion G driftWeight H.fields) (hν : C.norm = H.norm)
    (φ : G2.GroupMollifier G H.norm) (U : Opens (Fin N → ℝ))
    (a : ℝ≥0) (ha : 0 < (a : ℝ)) (θ : ℝ) (hθ : 0 ≤ θ)
    (B : Fin q → Fin q → ℝ) (hB : ∀ i j, 0 ≤ B i j) :
    let V : Opens (Fin N → ℝ) := ⟨{x | C.norm x < 1}, isOpen_lt C.norm.gauge.1 continuous_const⟩
    letI metric : MetricSpace (ControlCarrier N) := gaugeMetric G C.norm C.constant_one C.symmetric
    (∀ F : ControlCarrier N → ℝ, Continuous F → HasCompactSupport F → tsupport F ⊆ (V : Set (Fin N → ℝ)) →
      @H2.BoundedHolder (ControlCarrier N) metric a univ F → ∀ i j,
      @H2.boundedHolderNorm (ControlCarrier N) metric a (V : Set (Fin N → ℝ))
        (fun x => H1.principalValueConvolution G C.norm
          (fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields j.succ) K)) F x) ≤
        ENNReal.ofReal (B i j) * @H2.boundedHolderNorm (ControlCarrier N) metric a (V : Set (Fin N → ℝ)) F) →
    ∀ f : (Fin N → ℝ) → ℝ,
      memHolderXCompact driftWeight H.fields (controlDistance univ driftWeight H.fields) U 2 a f →
      ∃ jet : List (Fin (q + 1)) → (Fin N → ℝ) → ℝ,
        jet [] = (U : Set (Fin N → ℝ)).indicator f ∧
        (∀ I, wordWeight driftWeight I ≤ 2 →
          hasIntrinsicWordDeriv H.fields ⊤ I ((U : Set (Fin N → ℝ)).indicator f) (jet I) ∧
          Continuous (jet I) ∧ HasCompactSupport (jet I)) ∧
        let F := fun x => jet [0] x + ∑ i : Fin q, jet [i.succ, i.succ] x
        (∑ i : Fin q, ∑ j : Fin q,
          @H2.holderSemi (ControlCarrier N) metric a univ (jet [i.succ, j.succ])) +
          ENNReal.ofReal θ * @H2.holderSemi (ControlCarrier N) metric a univ (jet [0]) ≤
          ((q : ℝ≥0∞)^2 + ENNReal.ofReal θ * (1 + (q : ℝ≥0∞))) * ENNReal.ofReal (secondJetHolderMax B (fundamentalCorrectionCoefficients G H K hQ)) *
            @H2.holderSemi (ControlCarrier N) metric a univ F := by
  classical
  let metric : MetricSpace (ControlCarrier N) := gaugeMetric G C.norm C.constant_one C.symmetric
  dsimp only
  intro hPV f hf
  obtain ⟨T, hTU, jet, hzero, hj⟩ :=
    exists_global_holder_intrinsic_jets_of_memHolderXCompact_of_controlNorm
      G U driftWeight H.fields (H.fields_smooth G) C 2 ha hf
  have hi := fun I hI => (hj I hI).1
  have hc := fun I hI => (hj I hI).2.1
  have hs := fun I hI => (hj I hI).2.2.1
  have hh := fun I hI => (hj I hI).2.2.2.2
  refine ⟨jet, hzero, fun I hI => ⟨hi I hI, hc I hI, hs I hI⟩, ?_⟩
  exact global_seminorm_estimate_of_unit_principal_value_bounds
    G H K hQ C hν φ a ha θ hθ B hB
    ((U : Set (Fin N → ℝ)).indicator f) jet hzero hi hc hs hh hPV

end RothschildStein.H3
