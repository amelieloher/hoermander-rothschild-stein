-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.HolderPositiveConstantAssembly
public import RothschildStein.H3.FundamentalSecondCenteredHolder

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped BigOperators NNReal ENNReal
namespace RothschildStein.H3

/-- The compact weight-two estimate has one positive constant
fixed before all centers of a ball of the specified radius. -/
theorem center_uniform_estimate_of_controlNorm {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H) (hQ : 2 < (G.homogeneousDimension : ℝ))
    (C : G2.ControlNormConclusion G driftWeight H.fields)
    (φ : G2.GroupMollifier G C.norm)
    (a : ℝ≥0) (ha : 0 < (a : ℝ))
    (ha1 : (a : ℝ) < 1) {R : ℝ} (hR : 0 < R) :
    ∃ C₁₁ : ℝ, 0 < C₁₁ ∧ ∀ z : Fin N → ℝ,
      let U := quasiballDomain G C.norm z R
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
          ENNReal.ofReal C₁₁ *
            holderENorm (controlDistance univ driftWeight H.fields) (a : ℝ) univ F := by
  classical
  let metric : MetricSpace (ControlCarrier N) :=
    gaugeMetric G C.norm C.constant_one C.symmetric
  obtain ⟨B, hB, hPV⟩ := exists_fundamental_second_centered_PV_holder_bounds_of_controlNorm
    G H K C ha ha1 hR
  refine ⟨weightTwoHolderConstant B (controlCorrectionCoefficients G H K C hQ),
    weightTwoHolderConstant_pos _ _, ?_⟩
  intro z U f hf
  obtain ⟨jet, hz, hi, hsource⟩ := full_estimate_with_source_of_control_PV_bounds
    G H K hQ C φ U a ha B hB (by
      intro F hF hc hs hfinite i j
      have hfinite' : holderENorm (controlDistance univ driftWeight H.fields) a univ F < ⊤ := by
        rw [frozen_holderENorm_eq_control_norm G driftWeight H.fields C]
        exact hfinite
      have hb := hPV z F hF hc hs hfinite' i j
      rw [frozen_holderENorm_eq_control_norm G driftWeight H.fields C,
        frozen_holderENorm_eq_control_norm G driftWeight H.fields C] at hb
      exact hb) f hf
  refine ⟨jet, hz, hi, ?_⟩
  dsimp only at hsource ⊢
  rcases hsource with ⟨hclass, heq, hb⟩
  refine ⟨hclass, heq, ?_⟩
  rw [ofReal_weightTwoHolderConstant]
  exact hb

end RothschildStein.H3
