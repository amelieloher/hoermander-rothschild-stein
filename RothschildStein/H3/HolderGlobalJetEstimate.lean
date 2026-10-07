-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.CanonicalHolderEstimate
public import RothschildStein.H3.CompactGaugeHolderInput
public import RothschildStein.S.IntrinsicUniqueness
public import RothschildStein.H3.ControlMetric

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped BigOperators ENNReal NNReal
namespace RothschildStein.H3

/-- Compact gauge-Hölder inputs have finite auxiliary
norms in the fixed control metric used by the dilation estimate. -/
theorem boundedHolder_of_compact_gauge_holder {N : ℕ}
    (G : HomogeneousGroup N) (ν : G2.HomogeneousNorm G)
    (h1 : ν.c = 1) (hsym : ν.Symmetric) (a : ℝ≥0)
    {f : (Fin N → ℝ) → ℝ} (hc : Continuous f) (hs : HasCompactSupport f)
    {A : ℝ} (hh : ∀ x y, |f x - f y| ≤ A * G2.gaugeDistance G ν x y ^ (a : ℝ)) :
    letI metric : MetricSpace (ControlCarrier N) := gaugeMetric G ν h1 hsym
    @H2.BoundedHolder (ControlCarrier N) metric a univ (fun x : ControlCarrier N => f x) := by
  let metric : MetricSpace (ControlCarrier N) := gaugeMetric G ν h1 hsym
  obtain ⟨M, hM⟩ := hs.exists_bound_of_continuous hc
  have hs' : @H2.holderSup (ControlCarrier N) univ (fun x => f x) < ⊤ :=
    (H2.holderSup_le_of_bound (fun x _ => by simpa only [Real.norm_eq_abs] using hM x)).trans_lt
      ENNReal.ofReal_lt_top
  have hh' : @H2.holderSemi (ControlCarrier N) metric a univ (fun x => f x) < ⊤ := by
    apply lt_of_le_of_lt (H2.holderSemi_le_of_bound (abs_nonneg A) ?_) ENNReal.ofReal_lt_top
    intro x _ y _
    change |f x - f y| ≤ |A| * G2.gaugeDistance G ν x y ^ (a : ℝ)
    exact (hh x y).trans (mul_le_mul_of_nonneg_right (le_abs_self A)
      (Real.rpow_nonneg (ν.gauge.2.1 _) _))
  exact ENNReal.add_lt_top.mpr ⟨hs', hh'⟩

/-- Under the principal-value bounds, the compact intrinsic estimate
applies to any compact intrinsic jet family identified by intrinsic
uniqueness (BB p. 380). -/
theorem holder_estimate_for_global_jets_of_principal_value_bounds {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H) (hQ : 2 < (G.homogeneousDimension : ℝ))
    (C : G2.ControlNormConclusion G driftWeight H.fields) (hν : C.norm = H.norm)
    (φ : G2.GroupMollifier G H.norm) (U : Opens (Fin N → ℝ))
    (a : ℝ≥0) (ha : 0 < (a : ℝ)) (θ : ℝ) (hθ : 0 ≤ θ)
    (B : Fin q → Fin q → ℝ) (hB : ∀ i j, 0 ≤ B i j)
    (f : (Fin N → ℝ) → ℝ)
    (jet : List (Fin (q + 1)) → (Fin N → ℝ) → ℝ) (hzero : jet [] = f)
    (hi : ∀ I, wordWeight driftWeight I ≤ 2 → hasIntrinsicWordDeriv H.fields ⊤ I f (jet I))
    (hc : ∀ I, wordWeight driftWeight I ≤ 2 → Continuous (jet I))
    (hs : ∀ I, wordWeight driftWeight I ≤ 2 → HasCompactSupport (jet I))
    (hh : ∀ I, wordWeight driftWeight I ≤ 2 → ∃ A : ℝ, ∀ x y,
      |jet I x - jet I y| ≤ A * G2.gaugeDistance G C.norm x y ^ (a : ℝ))
    (hU : tsupport f ⊆ (U : Set (Fin N → ℝ))) :
    letI metric : MetricSpace (ControlCarrier N) := gaugeMetric G C.norm C.constant_one C.symmetric
    (∀ F : ControlCarrier N → ℝ, Continuous F → HasCompactSupport F → tsupport F ⊆ (U : Set (Fin N → ℝ)) →
      @H2.BoundedHolder (ControlCarrier N) metric a univ F → ∀ i j,
      @H2.boundedHolderNorm (ControlCarrier N) metric a (U : Set (Fin N → ℝ))
        (fun x => H1.principalValueConvolution G C.norm
          (fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields j.succ) K)) F x) ≤
        ENNReal.ofReal (B i j) * @H2.boundedHolderNorm (ControlCarrier N) metric a (U : Set (Fin N → ℝ)) F) →
    let F := fun x => jet [0] x + ∑ i : Fin q, jet [i.succ, i.succ] x
    (∑ i : Fin q, ∑ j : Fin q,
      @H2.boundedHolderNorm (ControlCarrier N) metric a univ (jet [i.succ, j.succ])) +
      ENNReal.ofReal θ * @H2.boundedHolderNorm (ControlCarrier N) metric a univ (jet [0]) ≤
      ((q : ℝ≥0∞)^2 + ENNReal.ofReal θ * (1 + (q : ℝ≥0∞))) *
        ENNReal.ofReal (secondJetHolderMax B (fundamentalCorrectionCoefficients G H K hQ)) *
        @H2.boundedHolderNorm (ControlCarrier N) metric a univ F := by
  classical
  let metric : MetricSpace (ControlCarrier N) := gaugeMetric G C.norm C.constant_one C.symmetric
  intro hPV
  have hf := memHolderXCompact_of_global_compact_gauge_jets G driftWeight H.fields C U
    2 ha.le jet hzero hi hc hs hh hU
  obtain ⟨v, hv0, hv, hb⟩ :=
    holder_estimate_with_canonical_constant_of_principal_value_bounds
      G H K hQ C hν φ U a ha θ hθ B hB hPV f hf
  have hind : (U : Set (Fin N → ℝ)).indicator f = f := by
    funext x
    by_cases hx : x ∈ (U : Set (Fin N → ℝ))
    · exact indicator_of_mem hx f
    · rw [indicator_of_notMem hx]
      exact (image_eq_zero_of_notMem_tsupport (fun h => hx (hU h))).symm
  rw [hind] at hv0 hv
  have he (I : List (Fin (q + 1))) (hI : wordWeight driftWeight I ≤ 2) : v I = jet I := by
    funext x
    exact S.hasIntrinsicWordDeriv_unique ⊤ H.fields I (hv I hI).1 (hi I hI) (mem_univ x)
  have hw0 : wordWeight (driftWeight (q := q)) [0] ≤ 2 := by simp [wordWeight, driftWeight]
  have hw2 (i j : Fin q) : wordWeight driftWeight [i.succ, j.succ] ≤ 2 := by
    simp [wordWeight, driftWeight]
  have hpair (i j : Fin q) := he [i.succ, j.succ] (hw2 i j)
  dsimp only at hb ⊢
  simpa only [he [0] hw0, hpair] using hb

end RothschildStein.H3
