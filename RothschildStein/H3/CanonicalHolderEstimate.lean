-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.HolderFixedEstimate
public import RothschildStein.H3.SecondJetHolderConstant

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped BigOperators ENNReal NNReal
namespace RothschildStein.H3

/-- A compact intrinsic input gives the horizontal-plus-drift estimate
under the global control-norm comparison and principal-value bounds.
Its coefficients are uniform in the input (BB Theorem 8.50, pp. 379–380). -/
theorem holder_estimate_with_canonical_constant_of_principal_value_bounds {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H) (hQ : 2 < (G.homogeneousDimension : ℝ))
    (C : G2.ControlNormConclusion G driftWeight H.fields) (hν : C.norm = H.norm)
    (φ : G2.GroupMollifier G H.norm) (U : Opens (Fin N → ℝ))
    (a : ℝ≥0) (ha : 0 < (a : ℝ)) (θ : ℝ) (hθ : 0 ≤ θ)
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
        (∑ i : Fin q, ∑ j : Fin q,
          @H2.boundedHolderNorm (ControlCarrier N) metric a univ (jet [i.succ, j.succ])) +
          ENNReal.ofReal θ * @H2.boundedHolderNorm (ControlCarrier N) metric a univ (jet [0]) ≤
          ((q : ℝ≥0∞)^2 + ENNReal.ofReal θ * (1 + (q : ℝ≥0∞))) * ENNReal.ofReal (secondJetHolderMax B (fundamentalCorrectionCoefficients G H K hQ)) *
            @H2.boundedHolderNorm (ControlCarrier N) metric a univ F := by
  exact holder_estimate_of_principal_value_bounds G H K hQ C hν φ U a ha θ
    (secondJetHolderMax B (fundamentalCorrectionCoefficients G H K hQ)) hθ
    (one_le_secondJetHolderMax B (fundamentalCorrectionCoefficients G H K hQ)) B hB
    (coefficient_le_secondJetHolderMax B (fundamentalCorrectionCoefficients G H K hQ) hB)

end RothschildStein.H3
