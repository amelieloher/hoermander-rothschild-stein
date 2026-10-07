-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.HolderFixedAssembly
public import RothschildStein.H3.HolderRealConstant

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped BigOperators ENNReal NNReal
namespace RothschildStein.H3

/-- The exact fixed estimate, source membership, and distribution
equation with one positive real constant fixed before the input. -/
theorem seminorm_estimate_with_positive_constant_of_control_PV_bounds {N q : ℕ}
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
    ∃ C₁₁ : ℝ, 0 < C₁₁ ∧ ∀ f : (Fin N → ℝ) → ℝ,
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
          ENNReal.ofReal C₁₁ *
            holderSeminorm (controlDistance univ driftWeight H.fields) (a : ℝ) univ F := by
  classical
  dsimp only
  intro hPV
  refine ⟨weightTwoHolderConstant B (controlCorrectionCoefficients G H K C hQ),
    weightTwoHolderConstant_pos _ _, ?_⟩
  intro f hf
  obtain ⟨jet, hz, hi, hsource⟩ := seminorm_estimate_with_source_of_control_PV_bounds
    G H K hQ C φ U a ha B hB hPV f hf
  refine ⟨jet, hz, hi, ?_⟩
  dsimp only at hsource ⊢
  rcases hsource with ⟨hclass, heq, hb⟩
  refine ⟨hclass, heq, ?_⟩
  rw [ofReal_weightTwoHolderConstant]
  exact hb

end RothschildStein.H3
