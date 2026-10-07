-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.WeightTwoFamilyEstimate
public import RothschildStein.H3.WeightTwoFamilySeminorm
public import RothschildStein.H3.HolderSourceClass
public import RothschildStein.H3.HolderSourceEquation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped BigOperators ENNReal NNReal
namespace RothschildStein.H3

/-- Fixed family estimate together with source-class membership
and the literal fixed distribution equation. Analytic PV inputs remain explicit. -/
theorem full_estimate_with_source_of_control_PV_bounds {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H) (hQ : 2 < (G.homogeneousDimension : ℝ))
    (C : G2.ControlNormConclusion G driftWeight H.fields)
    (φ : G2.GroupMollifier G C.norm) (U : Opens (Fin N → ℝ))
    (a : ℝ≥0) (ha : 0 < (a : ℝ))
    (B : Fin q → Fin q → ℝ) (hB : ∀ i j, 0 ≤ B i j) :
    letI metric : MetricSpace (ControlCarrier N) := gaugeMetric G C.norm C.constant_one C.symmetric
    (∀ F : ControlCarrier N → ℝ, Continuous F → HasCompactSupport F → tsupport F ⊆ (U : Set (Fin N → ℝ)) →
      @H2.BoundedHolder (ControlCarrier N) metric a univ F → ∀ i j,
      @H2.boundedHolderNorm (ControlCarrier N) metric a (U : Set (Fin N → ℝ))
        (fun x => H1.principalValueConvolution G C.norm
          (fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields j.succ) K)) F x) ≤
        ENNReal.ofReal (B i j) * @H2.boundedHolderNorm (ControlCarrier N) metric a (U : Set (Fin N → ℝ)) F) →
    ∀ f : (Fin N → ℝ) → ℝ,
      memHolderXCompact driftWeight H.fields (controlDistance univ driftWeight H.fields) U 2 a f →
      ∃ jet : List (Fin (q + 1)) → (Fin N → ℝ) → ℝ,
        jet [] = (U : Set (Fin N → ℝ)).indicator f ∧
        (∀ I, wordWeight driftWeight I ≤ 2 →
          hasIntrinsicWordDeriv H.fields ⊤ I ((U : Set (Fin N → ℝ)).indicator f) (jet I) ∧
          Continuous (jet I) ∧ HasCompactSupport (jet I)) ∧
        let F := fun x => jet [0] x + ∑ i : Fin q, jet [i.succ, i.succ] x
        memHolderX driftWeight H.fields (controlDistance univ driftWeight H.fields) ⊤ 0 a F ∧
        hasDistributionEquationWithDrift ⊤ H.fields (fun i => (H.fields_smooth G i).contDiffOn)
          (Distribution.ofFun ⊤ ((U : Set (Fin N → ℝ)).indicator f) volume (⊤ : ℕ∞)) F ∧
        (∑ I ∈ driftSecondWordFamily q,
          intrinsicWordENorm H.fields (controlDistance univ driftWeight H.fields) ⊤ I (a : ℝ)
            ((U : Set (Fin N → ℝ)).indicator f)) ≤
          ((q : ℝ≥0∞)^2 + (1 + (q : ℝ≥0∞))) * ENNReal.ofReal (secondJetHolderMax B (controlCorrectionCoefficients G H K C hQ)) *
            holderENorm (controlDistance univ driftWeight H.fields) (a : ℝ) univ F := by
  classical
  dsimp only
  intro hPV f hf
  obtain ⟨jet, hz, hi, hb⟩ := weight_two_family_estimate_of_control_PV_bounds
    G H K hQ C φ U a ha B hB hPV f hf
  refine ⟨jet, hz, hi, ?_⟩
  dsimp only at hb ⊢
  refine ⟨source_memHolderX_of_compact_input G H.fields (H.fields_smooth G)
    C U a ha f hf jet (fun I hI => (hi I hI).1), ?_, hb⟩
  exact source_distribution_equation_of_intrinsic_jets H.fields (H.fields_smooth G)
    ((U : Set (Fin N → ℝ)).indicator f) jet hz
    (fun I hI => (hi I hI).1) (fun I hI => (hi I hI).2.1)
    (fun I hI => (hi I hI).2.2)

/-- Fixed family estimate together with source-class membership
and the literal fixed distribution equation. Analytic PV inputs remain explicit. -/
theorem seminorm_estimate_with_source_of_control_PV_bounds {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H) (hQ : 2 < (G.homogeneousDimension : ℝ))
    (C : G2.ControlNormConclusion G driftWeight H.fields)
    (φ : G2.GroupMollifier G C.norm) (U : Opens (Fin N → ℝ))
    (a : ℝ≥0) (ha : 0 < (a : ℝ))
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
        memHolderX driftWeight H.fields (controlDistance univ driftWeight H.fields) ⊤ 0 a F ∧
        hasDistributionEquationWithDrift ⊤ H.fields (fun i => (H.fields_smooth G i).contDiffOn)
          (Distribution.ofFun ⊤ ((U : Set (Fin N → ℝ)).indicator f) volume (⊤ : ℕ∞)) F ∧
        (∑ I ∈ driftSecondWordFamily q,
          holderSeminorm (controlDistance univ driftWeight H.fields) (a : ℝ) univ (jet I)) ≤
          ((q : ℝ≥0∞)^2 + (1 + (q : ℝ≥0∞))) * ENNReal.ofReal (secondJetHolderMax B (controlCorrectionCoefficients G H K C hQ)) *
            holderSeminorm (controlDistance univ driftWeight H.fields) (a : ℝ) univ F := by
  classical
  dsimp only
  intro hPV f hf
  obtain ⟨jet, hz, hi, hb⟩ := weight_two_family_seminorm_of_control_PV_bounds
    G H K hQ C φ U a ha B hB hPV f hf
  refine ⟨jet, hz, hi, ?_⟩
  dsimp only at hb ⊢
  refine ⟨source_memHolderX_of_compact_input G H.fields (H.fields_smooth G)
    C U a ha f hf jet (fun I hI => (hi I hI).1), ?_, hb⟩
  exact source_distribution_equation_of_intrinsic_jets H.fields (H.fields_smooth G)
    ((U : Set (Fin N → ℝ)).indicator f) jet hz
    (fun I hI => (hi I hI).1) (fun I hI => (hi I hI).2.1)
    (fun I hI => (hi I hI).2.2)

end RothschildStein.H3
