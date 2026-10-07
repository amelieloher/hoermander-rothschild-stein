-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.HolderPotentialLimit
public import RothschildStein.H3.IntrinsicHolderDriftEquation
public import RothschildStein.H3.IntrinsicJetFullNorm
public import RothschildStein.H3.IntrinsicWordInputCongruence

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal BigOperators
namespace RothschildStein.H3

/-- The fundamental convolution solves the problem on the chosen open
domain under the smooth-source estimate (⋆). The positive full-norm
constant is uniform in the source, and the equation is interpreted in
distributions. -/
theorem frozen_holder_potential_solver_of_smooth_source_estimates {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H) (hQ : 2 < (G.homogeneousDimension : ℝ))
    (C : G2.ControlNormConclusion G driftWeight H.fields)
    (φ : G2.GroupMollifier G C.norm) (U : Opens (Fin N → ℝ))
    {ρ : ℝ} {a : ℝ≥0} (ha : 0 < a)
    (hestimate : ∀ t : ℝ≥0, 0 < t → t ≤ a → ∃ A : ℝ, 0 < A ∧
      ∀ h : (Fin N → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) h →
      HasCompactSupport h → tsupport h ⊆ {x | C.norm x < ρ} →
      holderXENorm driftWeight H.fields (controlDistance univ driftWeight H.fields)
        U 2 t (G2.groupConvolution G h K) ≤ ENNReal.ofReal A *
          holderENorm (controlDistance univ driftWeight H.fields) t univ h) :
    ∃ A : ℝ, 0 < A ∧ ∀ f : (Fin N → ℝ) → ℝ,
      Continuous f → HasCompactSupport f → tsupport f ⊆ {x | C.norm x < ρ} →
      holderENorm (controlDistance univ driftWeight H.fields) a univ f < ⊤ →
      memHolderX driftWeight H.fields (controlDistance univ driftWeight H.fields)
        U 2 a (G2.groupConvolution G f K) ∧
      hasDistributionEquationWithDrift U H.fields (fun i => (H.fields_smooth G i).contDiffOn)
        (Distribution.ofFun U (G2.groupConvolution G f K) volume (⊤ : ℕ∞)) f ∧
      holderXENorm driftWeight H.fields (controlDistance univ driftWeight H.fields)
        U 2 a (G2.groupConvolution G f K) ≤ ENNReal.ofReal A *
          holderENorm (controlDistance univ driftWeight H.fields) a univ f := by
  classical
  let d := controlDistance univ driftWeight H.fields
  let D := controlDistanceGeometry_of_controlNorm G driftWeight H.fields C
  obtain ⟨A, hA, hsolve⟩ :=
    exists_uniform_holder_potential_limit_of_smooth_source_estimates G H K hQ C φ U ha hestimate
  let c : ℝ := ((wordFamily (driftWeight (q := q)) 2).card : ℝ) + 1
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c * 2 * A, by positivity, ?_⟩
  intro f hf hcf hs hfinite
  obtain ⟨jet, hmem, hid, heq, hj⟩ := hsolve f hf hcf hs hfinite
  let M := 2 * ENNReal.ofReal A * holderENorm d a univ f
  have hM : M < ⊤ := ENNReal.mul_lt_top
    (ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top) hfinite
  have hjet (I : List (Fin (q + 1))) (hI : wordWeight (driftWeight (q := q)) I ≤ 2) :
      holderENorm d a (U : Set (Fin N → ℝ)) (jet I) < ⊤ := (hj I hI).2.trans_lt hM
  have hactual (I : List (Fin (q + 1))) (hI : wordWeight (driftWeight (q := q)) I ≤ 2) :
      hasIntrinsicWordDeriv H.fields U I (G2.groupConvolution G f K) (jet I) :=
    intrinsic_word_congr_input H.fields U I hid (hj I hI).1
  have hm : memHolderX driftWeight H.fields d U 2 a (G2.groupConvolution G f K) := by
    refine ⟨?_, ?_⟩
    · rw [← S.holderENorm_congr d a (U : Set (Fin N → ℝ)) (jet []) hid]
      exact hmem.1
    · intro I hI
      have hi := (S.mem_wordFamily_iff driftWeight 2 I).mp hI
      exact ⟨jet I, hactual I hi, hjet I hi⟩
  have hdist := frozen_drift_equation_of_intrinsic_holder_jets ⊤ U D (subset_univ _)
    H.fields (fun i => (H.fields_smooth G i).contDiffOn) ha (jet []) jet rfl
    (fun I hI => ⟨(hj I hI).1, hjet I hI⟩) f hf.continuousOn heq
  have hae : jet [] =ᵐ[volume.restrict (U : Set (Fin N → ℝ))] G2.groupConvolution G f K := by
    filter_upwards [ae_restrict_mem U.isOpen.measurableSet] with x hx
    exact hid hx
  have hd := Distribution.ofFun_congr_ae (n := (⊤ : ℕ∞)) hae
  rw [hd] at hdist
  refine ⟨hm, hdist, ?_⟩
  have hb := holderXENorm_le_card_mul_of_intrinsic_jets driftWeight H.fields d U 2 a
    (G2.groupConvolution G f K) jet hactual M (fun I hI => (hj I hI).2)
  have hcard : ((wordFamily (driftWeight (q := q)) 2).card : ℝ≥0∞) ≤ ENNReal.ofReal c := by
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal
      (show ((wordFamily (driftWeight (q := q)) 2).card : ℝ) ≤ c by dsimp [c]; linarith)
  have he : ENNReal.ofReal (c * 2 * A) = ENNReal.ofReal c * 2 * ENNReal.ofReal A := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hc.le]
    norm_num
  calc
    _ ≤ ((wordFamily (driftWeight (q := q)) 2).card : ℝ≥0∞) * M := hb
    _ ≤ ENNReal.ofReal c * M := mul_le_mul' hcard le_rfl
    _ = _ := by rw [he]; simp only [M, d, mul_assoc]

end RothschildStein.H3
