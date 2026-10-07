-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.HolderGlobalJetEstimate
public import RothschildStein.H3.CompactJetDilationInput
public import RothschildStein.H3.FiniteHolderDilationLimit
public import RothschildStein.H2.HolderFiniteSum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped BigOperators ENNReal NNReal
namespace RothschildStein.H3

/-- Actual unit-ball principal-value estimates imply the
global seminorm estimate for compact intrinsic jets. All dilations,
support thresholds and limiting steps are constructed (BB p. 380). -/
theorem global_seminorm_estimate_of_unit_principal_value_bounds {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H) (hQ : 2 < (G.homogeneousDimension : ℝ))
    (C : G2.ControlNormConclusion G driftWeight H.fields) (hν : C.norm = H.norm)
    (φ : G2.GroupMollifier G H.norm)
    (a : ℝ≥0) (ha : 0 < (a : ℝ)) (θ : ℝ) (hθ : 0 ≤ θ)
    (B : Fin q → Fin q → ℝ) (hB : ∀ i j, 0 ≤ B i j)
    (f : (Fin N → ℝ) → ℝ)
    (jet : List (Fin (q + 1)) → (Fin N → ℝ) → ℝ) (hzero : jet [] = f)
    (hi : ∀ I, wordWeight driftWeight I ≤ 2 → hasIntrinsicWordDeriv H.fields ⊤ I f (jet I))
    (hc : ∀ I, wordWeight driftWeight I ≤ 2 → Continuous (jet I))
    (hs : ∀ I, wordWeight driftWeight I ≤ 2 → HasCompactSupport (jet I))
    (hh : ∀ I, wordWeight driftWeight I ≤ 2 → ∃ A : ℝ, ∀ x y,
      |jet I x - jet I y| ≤ A * G2.gaugeDistance G C.norm x y ^ (a : ℝ)) :
    let U : Opens (Fin N → ℝ) := ⟨{x | C.norm x < 1}, isOpen_lt C.norm.gauge.1 continuous_const⟩
    letI metric : MetricSpace (ControlCarrier N) := gaugeMetric G C.norm C.constant_one C.symmetric
    (∀ F : ControlCarrier N → ℝ, Continuous F → HasCompactSupport F → tsupport F ⊆ (U : Set (Fin N → ℝ)) →
      @H2.BoundedHolder (ControlCarrier N) metric a univ F → ∀ i j,
      @H2.boundedHolderNorm (ControlCarrier N) metric a (U : Set (Fin N → ℝ))
        (fun x => H1.principalValueConvolution G C.norm
          (fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields j.succ) K)) F x) ≤
        ENNReal.ofReal (B i j) * @H2.boundedHolderNorm (ControlCarrier N) metric a (U : Set (Fin N → ℝ)) F) →
    let F := fun x => jet [0] x + ∑ i : Fin q, jet [i.succ, i.succ] x
    (∑ i : Fin q, ∑ j : Fin q,
      @H2.holderSemi (ControlCarrier N) metric a univ (jet [i.succ, j.succ])) +
      ENNReal.ofReal θ * @H2.holderSemi (ControlCarrier N) metric a univ (jet [0]) ≤
      ((q : ℝ≥0∞)^2 + ENNReal.ofReal θ * (1 + (q : ℝ≥0∞))) *
        ENNReal.ofReal (secondJetHolderMax B (fundamentalCorrectionCoefficients G H K hQ)) *
        @H2.holderSemi (ControlCarrier N) metric a univ F := by
  classical
  let U : Opens (Fin N → ℝ) := ⟨{x | C.norm x < 1}, isOpen_lt C.norm.gauge.1 continuous_const⟩
  let metric : MetricSpace (ControlCarrier N) := gaugeMetric G C.norm C.constant_one C.symmetric
  dsimp only
  intro hPV
  let F : ControlCarrier N → ℝ := fun x => jet [0] x + ∑ i : Fin q, jet [i.succ, i.succ] x
  let c : ℝ≥0∞ := ((q : ℝ≥0∞)^2 + ENNReal.ofReal θ * (1 + (q : ℝ≥0∞))) *
    ENNReal.ofReal (secondJetHolderMax B (fundamentalCorrectionCoefficients G H K hQ))
  have hct : c ≠ ⊤ := by
    dsimp only [c]
    finiteness
  have hw0 : wordWeight (driftWeight (q := q)) [0] ≤ 2 := by simp [wordWeight, driftWeight]
  have hw2 (i j : Fin q) : wordWeight driftWeight [i.succ, j.succ] ≤ 2 := by
    simp [wordWeight, driftWeight]
  have hnil : wordWeight (driftWeight (q := q)) [] ≤ 2 := by simp [wordWeight]
  have hb (I : List (Fin (q + 1))) (hI : wordWeight driftWeight I ≤ 2) :
      @H2.BoundedHolder (ControlCarrier N) metric a univ (fun x => jet I x) := by
    obtain ⟨A, hA⟩ := hh I hI
    exact boundedHolder_of_compact_gauge_holder G C.norm C.constant_one C.symmetric a
      (hc I hI) (hs I hI) hA
  have hFb : @H2.BoundedHolder (ControlCarrier N) metric a univ F := by
    have hsum := @H2.boundedHolder_sum (ControlCarrier N) metric (Fin q)
      Finset.univ a univ (fun i x => jet [i.succ, i.succ] x)
      (fun i _ => hb _ (hw2 i i))
    have hsumb : @H2.BoundedHolder (ControlCarrier N) metric a univ
        (fun x : ControlCarrier N => ∑ i : Fin q, jet [i.succ, i.succ] x) := by
      exact hsum
    have he : ((fun x : ControlCarrier N => jet [0] x) +
        (fun x : ControlCarrier N => ∑ i : Fin q, jet [i.succ, i.succ] x)) = F := by
      funext x
      rfl
    exact he ▸ (hb [0] hw0).add hsumb
  let J := Option (Fin q × Fin q)
  let weight : J → ℝ≥0∞ := fun j => match j with | none => ENNReal.ofReal θ | some _ => 1
  let u : J → ControlCarrier N → ℝ := fun j => match j with
    | none => fun x => jet [0] x
    | some ij => fun x => jet [ij.1.succ, ij.2.succ] x
  have hweight : ∀ j, weight j ≠ ⊤ := by
    intro j
    cases j <;> simp [weight]
  have hu : ∀ j, @H2.BoundedHolder (ControlCarrier N) metric a univ (u j) := by
    intro j
    cases j with
    | none => exact hb [0] hw0
    | some ij => exact hb _ (hw2 ij.1 ij.2)
  obtain ⟨R0, _hR0, hsupp⟩ := exists_unit_ball_dilation_scale G C.norm (hzero ▸ hs [] hnil)
  have hscaled : ∀ R : ℝ, R0 ≤ R → 0 < R →
      (∑ j, weight j * @H2.boundedHolderNorm (ControlCarrier N) metric a univ
        (fun x : ControlCarrier N => R ^ 2 * u j (G.dilate R x))) ≤
      c * @H2.boundedHolderNorm (ControlCarrier N) metric a univ
        (fun x : ControlCarrier N => R ^ 2 * F (G.dilate R x)) := by
    intro R hR hp
    let scaled := fun I x => R ^ (wordWeight driftWeight I : ℝ) * jet I (G.dilate R x)
    obtain ⟨hz, hi', hc', hs'⟩ := compact_intrinsic_jets_dilate G H hp f jet hzero hi hc hs
    have hh' : ∀ I, wordWeight driftWeight I ≤ 2 → ∃ A : ℝ, ∀ x y,
        |scaled I x - scaled I y| ≤ A * G2.gaugeDistance G C.norm x y ^ (a : ℝ) := by
      intro I hI
      obtain ⟨A, hA⟩ := hh I hI
      exact ⟨R ^ (wordWeight driftWeight I : ℝ) * A * R ^ (a : ℝ),
        gauge_holder_dilate G C.norm hp _ a A (jet I) hA⟩
    have hbR := holder_estimate_for_global_jets_of_principal_value_bounds
      G H K hQ C hν φ U a ha θ hθ B hB (f ∘ G.dilate R) scaled hz hi' hc' hs' hh'
      (hsupp R hR).2 hPV
    have hzeroR : scaled [0] = fun x => R ^ 2 * jet [0] (G.dilate R x) := by
      funext x
      simp [scaled, wordWeight, driftWeight]
    have hpairR (i j : Fin q) : scaled [i.succ, j.succ] =
        fun x => R ^ 2 * jet [i.succ, j.succ] (G.dilate R x) := by
      funext x
      have hw : (wordWeight (driftWeight (q := q)) [i.succ, j.succ] : ℝ) = 2 := by
        norm_num [wordWeight, driftWeight]
      change R ^ (wordWeight driftWeight [i.succ, j.succ] : ℝ) * _ = _
      rw [hw, Real.rpow_two]
    have hsourceR : (fun x => scaled [0] x + ∑ i : Fin q, scaled [i.succ, i.succ] x) =
        fun x => R ^ 2 * F (G.dilate R x) := by
      funext x
      exact intrinsic_jet_source_dilate G R jet x
    dsimp only at hbR
    rw [hsourceR] at hbR
    simp_rw [hzeroR, hpairR] at hbR
    simpa only [metric, ControlCarrier, c, F, J, weight, u, Fintype.sum_option, Fintype.sum_prod_type, one_mul, add_comm] using hbR
  have hout := finite_holder_seminorm_bound_of_dilated_norm_bounds
    G C.norm C.constant_one C.symmetric a ha R0 c hct weight hweight u F hu hFb hscaled
  simpa only [metric, ControlCarrier, c, F, J, weight, u, Fintype.sum_option, Fintype.sum_prod_type, one_mul, add_comm] using hout

end RothschildStein.H3
