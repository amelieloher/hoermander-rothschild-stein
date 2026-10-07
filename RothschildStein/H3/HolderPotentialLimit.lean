-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.FrozenHolderSourceSequence
public import RothschildStein.H3.FrozenHolderLowerExponent
public import RothschildStein.H3.SmoothPotentialJetCauchy
public import RothschildStein.H3.ControlDistanceGeometry
public import RothschildStein.H3.HolderJetCompleteness
public import RothschildStein.H3.ConvolutionLimitIdentification
public import RothschildStein.H3.PointwiseDriftSourceLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter TopologicalSpace
open scoped Topology ENNReal NNReal BigOperators
namespace RothschildStein.H3

/-- The smooth-source estimate (⋆), at each positive exponent up to a,
gives compatible intrinsic jets whose limit is the fundamental convolution
and satisfies the source equation pointwise. -/
theorem exists_uniform_holder_potential_limit_of_smooth_source_estimates {N q : ℕ}
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
          holderENorm (controlDistance univ driftWeight H.fields) t univ h)
    : ∃ A : ℝ, 0 < A ∧ ∀ f : (Fin N → ℝ) → ℝ,
      Continuous f → HasCompactSupport f →
      tsupport f ⊆ {x | C.norm x < ρ} →
      holderENorm (controlDistance univ driftWeight H.fields) a univ f < ⊤ →
      ∃ jet : List (Fin (q + 1)) → (Fin N → ℝ) → ℝ,
      memHolderX driftWeight H.fields (controlDistance univ driftWeight H.fields) U 2 a (jet []) ∧
      EqOn (jet []) (G2.groupConvolution G f K) (U : Set (Fin N → ℝ)) ∧
      EqOn (fun x => jet [0] x + ∑ i : Fin q, jet [i.succ, i.succ] x) f
        (U : Set (Fin N → ℝ)) ∧
      ∀ I, wordWeight (driftWeight (q := q)) I ≤ 2 →
        hasIntrinsicWordDeriv H.fields U I (jet []) (jet I) ∧
        holderENorm (controlDistance univ driftWeight H.fields) a (U : Set (Fin N → ℝ)) (jet I) ≤
          2 * ENNReal.ofReal A * holderENorm (controlDistance univ driftWeight H.fields) a univ f := by
  classical
  let d := controlDistance univ driftWeight H.fields
  let D := controlDistanceGeometry_of_controlNorm G driftWeight H.fields C
  let b : ℝ≥0 := a / 2
  have hb : 0 < b := half_pos ha
  have hba : b < a := half_lt_self ha
  obtain ⟨A, hA, hAest⟩ := hestimate a ha le_rfl
  obtain ⟨B, _hB, hBest⟩ := hestimate b hb hba.le
  refine ⟨A, hA, ?_⟩
  intro f hf hc hs hfinite
  obtain ⟨F, hF, hconv, hbound, hdiff⟩ :=
    exists_fixed_holder_source_sequence_of_controlNorm G driftWeight H.fields C φ ha hf hc hs hfinite
  let jets := fun n I => wordDerivative H.fields I (G2.groupConvolution G (F n) K)
  let M := ENNReal.ofReal A * holderENorm d a univ f
  have hM : M < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfinite
  have hnorm (n : ℕ) (I : List (Fin (q + 1)))
      (hI : wordWeight (driftWeight (q := q)) I ≤ 2) :
      holderENorm d a (U : Set (Fin N → ℝ)) (jets n I) ≤ M := by
    exact (smooth_fundamental_potential_jet_norm_le G H K hQ (F n)
      (hF n).1 (hF n).2.1 U d 2 a I hI).trans
      ((hAest (F n) (hF n).1 (hF n).2.1 (hF n).2.2).trans
        (mul_le_mul' le_rfl (hbound n)))
  have hnormb (n : ℕ) (I : List (Fin (q + 1)))
      (hI : wordWeight (driftWeight (q := q)) I ≤ 2) :
      holderENorm d b (U : Set (Fin N → ℝ)) (jets n I) < ⊤ :=
    fixed_holder_lower_exponent_finite_of_controlNorm G driftWeight H.fields C ha hba.le
      (U : Set (Fin N → ℝ)) (jets n I) ((hnorm n I hI).trans_lt hM)
  have hcauchy (I : List (Fin (q + 1)))
      (hI : wordWeight (driftWeight (q := q)) I ≤ 2) :
      S.holderCauchySeq d b (U : Set (Fin N → ℝ)) (fun n => jets n I) :=
    smooth_potential_jet_cauchy_of_smooth_source_estimate G H K hQ U
      {x | C.norm x < ρ} d 2 b B hBest F hF (hdiff b hba) I hI
  obtain ⟨jet, hmem, hj⟩ := exists_holder_jet_limit_of_cauchy ⊤ U D
    (subset_univ _) driftWeight H.fields 2 ha hb jets
    (fun n I _ => smooth_fundamental_potential_intrinsic_on G H K hQ (F n)
      (hF n).1 (hF n).2.1 U I) hnormb hcauchy (fun _ => M)
    (fun _ _ => hM) hnorm
  have hzero : wordWeight (driftWeight (q := q)) [] ≤ 2 := by simp [wordWeight]
  let S := G2.gaugeClosedBall G C.norm 0 ρ
  have hsS : tsupport f ⊆ S := by
    intro x hx
    change C.norm (G.mul (G.inv 0) x) ≤ ρ
    rw [G2.inv_zero, G2.zero_mul]
    exact (hs hx).le
  have hFS (n : ℕ) : tsupport (F n) ⊆ S := by
    intro x hx
    change C.norm (G.mul (G.inv 0) x) ≤ ρ
    rw [G2.inv_zero, G2.zero_mul]
    exact ((hF n).2.2 hx).le
  have hid := groupConvolution_eqOn_of_uniform_source_and_pointwise_limits G K f
    K.locallyIntegrable hf S (G2.isCompact_gaugeClosedBall G C.norm.gauge 0 ρ)
    ((subset_tsupport f).trans hsS) F (fun n => jets n []) (jet [])
    (fun n => ⟨(hF n).1.continuous, (subset_tsupport (F n)).trans (hFS n)⟩)
    hconv (fun _ => rfl) (U : Set (Fin N → ℝ)) (hj [] hzero).2.2.2.2
  have heq := drift_source_eqOn_of_pointwise_jet_limits U jets jet F f
    (fun I hI => (hj I hI).2.2.2.2)
    (fun x _ => hconv.tendsto_at x)
    (fun n x _ => congrFun (smooth_fundamental_potential_jets G H K hQ (F n)
      (hF n).1 (hF n).2.1).2.2.2 x)
  refine ⟨jet, hmem, hid, heq, ?_⟩
  intro I hI
  refine ⟨(hj I hI).1, ?_⟩
  have hh := (hj I hI).2.1
  change holderENorm d a (U : Set (Fin N → ℝ)) (jet I) ≤ _ at hh ⊢
  simpa only [M, two_mul, add_mul] using hh

end RothschildStein.H3
