-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.HolderFixedNormEstimate
public import RothschildStein.S.IntrinsicNormRepresentatives

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped BigOperators ENNReal NNReal
namespace RothschildStein.H3

/-- The estimate uses the fixed intrinsic word norms of the jet
representatives under the global control-norm comparison and principal-value
bounds (BB Theorem 8.50, p. 380). -/
theorem intrinsic_word_estimate_of_control_PV_bounds {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H) (hQ : 2 < (G.homogeneousDimension : ℝ))
    (C : G2.ControlNormConclusion G driftWeight H.fields)
    (φ : G2.GroupMollifier G C.norm) (U : Opens (Fin N → ℝ))
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
          intrinsicWordENorm H.fields (controlDistance univ driftWeight H.fields) ⊤ [i.succ, j.succ] (a : ℝ) ((U : Set (Fin N → ℝ)).indicator f)) +
          ENNReal.ofReal θ * intrinsicWordENorm H.fields (controlDistance univ driftWeight H.fields) ⊤ [0] (a : ℝ) ((U : Set (Fin N → ℝ)).indicator f) ≤
          ((q : ℝ≥0∞)^2 + ENNReal.ofReal θ * (1 + (q : ℝ≥0∞))) * ENNReal.ofReal (secondJetHolderMax B (controlCorrectionCoefficients G H K C hQ)) *
            holderENorm (controlDistance univ driftWeight H.fields) (a : ℝ) univ F := by
  classical
  dsimp only
  intro hPV f hf
  obtain ⟨jet, hz, hi, hb⟩ := fixed_holder_estimate_of_control_PV_bounds
    G H K hQ C φ U a ha θ hθ B hB hPV f hf
  refine ⟨jet, hz, hi, ?_⟩
  dsimp only at hb ⊢
  have he (I : List (Fin (q + 1))) (hI : wordWeight driftWeight I ≤ 2) :
      intrinsicWordENorm H.fields (controlDistance univ driftWeight H.fields) ⊤ I (a : ℝ)
        ((U : Set (Fin N → ℝ)).indicator f) =
      holderENorm (controlDistance univ driftWeight H.fields) (a : ℝ) univ (jet I) :=
    S.intrinsicWordENorm_eq_representative ⊤ H.fields _ I a _ _ (hi I hI).1
  have hw0 : wordWeight (driftWeight (q := q)) [0] ≤ 2 := by simp [wordWeight, driftWeight]
  have hw2 (i j : Fin q) : wordWeight driftWeight [i.succ, j.succ] ≤ 2 := by
    simp [wordWeight, driftWeight]
  have hpair (i j : Fin q) := he [i.succ, j.succ] (hw2 i j)
  simp_rw [he [0] hw0, hpair]
  exact hb

end RothschildStein.H3
