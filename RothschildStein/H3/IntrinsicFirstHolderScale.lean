-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.IntrinsicNearFarSplit
public import RothschildStein.H3.FundamentalNearBounds
public import RothschildStein.H3.FundamentalFarBounds
public import RothschildStein.H3.PositiveRepresentation
public import RothschildStein.H3.HolderBoundary

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal NNReal BigOperators
namespace RothschildStein.H3

/-- The first-order Hölder norm of compact intrinsic order-two jets
satisfies the near/far scale estimate under the global control-norm
hypotheses. Both constants are uniform in the center, input, jet family,
and scale; the source is the drift-plus-diagonal jet sum. -/
theorem intrinsic_first_holder_scale_of_controlNorm {N q : ℕ} (G : HomogeneousGroup N)
    (H : H1.StandingHypotheses G q) (K : H1.FundamentalKernel G H)
    (Hc : G2.ControlNormConclusion G driftWeight H.fields)
    (hQ : 2 < (G.homogeneousDimension : ℝ)) (μ : G2.GroupMollifier G H.norm)
    (ν : G2.HomogeneousNorm G) (hν : ν.Smooth)
    {α : ℝ≥0} (hα : 0 < α) (hα1 : (α : ℝ) < 1) {ρ : ℝ} (hρ : 0 < ρ) :
    let metric : MetricSpace (ControlCarrier N) :=
      gaugeMetric G Hc.norm Hc.constant_one Hc.symmetric
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ z : ControlCarrier N,
      ∀ u : (Fin N → ℝ) → ℝ,
      ∀ jet : List (Fin (q + 1)) → (Fin N → ℝ) → ℝ,
      jet [] = u →
      (∀ I, wordWeight driftWeight I ≤ 2 → hasIntrinsicWordDeriv H.fields ⊤ I u (jet I)) →
      (∀ I, wordWeight driftWeight I ≤ 2 → Continuous (jet I)) →
      (∀ I, wordWeight driftWeight I ≤ 2 → HasCompactSupport (jet I)) →
      (∀ I, wordWeight driftWeight I ≤ 2 → tsupport (jet I) ⊆ G2.gaugeBall G Hc.norm z ρ) →
      ∀ ε : ℝ, 0 < ε → ε < 1 →
      let F := fun y => jet [0] y + ∑ i : Fin q, jet [i.succ, i.succ] y
      @H2.boundedHolderNorm (ControlCarrier N) metric α univ (fun x => u x) +
        (∑ i : Fin q, @H2.boundedHolderNorm (ControlCarrier N) metric α univ
          (fun x => jet [i.succ] x)) ≤
        ENNReal.ofReal (a * ε ^ ((1 - (α : ℝ)) / 2) * lpNorm F ∞ volume) +
        ENNReal.ofReal (b * ε ^ (-3 - (G.homogeneousDimension : ℝ)) * lpNorm u ∞ volume) := by
  classical
  let metric : MetricSpace (ControlCarrier N) :=
    gaugeMetric G Hc.norm Hc.constant_one Hc.symmetric
  obtain ⟨a, ha, hnear⟩ := fundamental_near_convolution_bounds_of_controlNorm G H K Hc hQ ν hν hα hα1 hρ
  obtain ⟨c, hcpos, hfar⟩ := fundamental_far_convolution_bounds_of_controlNorm G H K Hc hQ ν hν hα1.le
  let v := (volume (G2.gaugeBall G Hc.norm 0 ρ)).toReal
  let b := c * v + 1
  have hv : 0 ≤ v := ENNReal.toReal_nonneg
  have hb : 0 < b := by dsimp [b]; nlinarith [mul_nonneg hcpos.le hv]
  refine ⟨a, b, ha, hb, ?_⟩
  intro z u jet hzero hi hc hs hsupport ε hε hε1
  let F := fun y => jet [0] y + ∑ i : Fin q, jet [i.succ, i.succ] y
  let A : Set (ControlCarrier N) := ball z ρ
  let R := sumSquaresWithDrift (fun i => G2.rightField G (H.fields i 0))
  let near := fun (T : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) => G2.groupConvolution G F
    (fun w => smoothQuasiballCutoff G ν 0 (ε / 2) ε w * T w) x
  let far := fun (T : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) => G2.groupConvolution G u
    (R (exteriorCutoffKernel ν interpolationCutoffProfile T ε)) x
  let normA := fun f : (Fin N → ℝ) → ℝ =>
    @H2.boundedHolderNorm (ControlCarrier N) metric α A (fun x => f x)
  let normG := fun f : (Fin N → ℝ) → ℝ =>
    @H2.boundedHolderNorm (ControlCarrier N) metric α univ (fun x => f x)
  have hw0 : wordWeight (driftWeight (q := q)) [] ≤ 2 := by simp [wordWeight]
  have hw1 (i : Fin q) : wordWeight (driftWeight (q := q)) [i.succ] ≤ 2 := by
    simp [wordWeight, driftWeight]
  have hu : Continuous u := hzero ▸ hc [] hw0
  have hsu : HasCompactSupport u := hzero ▸ hs [] hw0
  have hsuA : tsupport u ⊆ G2.gaugeBall G Hc.norm z ρ := hzero ▸ hsupport [] hw0
  have hdata := intrinsicJetSource_data jet hc hs hsupport
  have hn := hnear z F (hdata.1.memLp_of_hasCompactSupport hdata.2.1) hdata.2.2 ε hε hε1
  have hf := hfar u hu hsu ε hε hε1
  have hm := integral_abs_le_gaugeBall_mass G Hc.norm hρ hu hsu z hsuA
  have hp : 0 ≤ ε ^ (-3 - (G.homogeneousDimension : ℝ)) := Real.rpow_nonneg hε.le _
  have hf' : normG (far K) + (∑ i : Fin q, normG (far (fieldDerivative (H.fields i.succ) K))) ≤
      ENNReal.ofReal (b * ε ^ (-3 - (G.homogeneousDimension : ℝ)) * lpNorm u ∞ volume) := by
    apply hf.trans
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ c * ε ^ (-3 - (G.homogeneousDimension : ℝ)) * (v * lpNorm u ∞ volume) :=
        mul_le_mul_of_nonneg_left hm (mul_nonneg hcpos.le hp)
      _ = (c * v) * ε ^ (-3 - (G.homogeneousDimension : ℝ)) * lpNorm u ∞ volume := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (show c * v ≤ b by dsimp [b]; linarith) hp) lpNorm_nonneg
  have hrep := positive_representation_of_compact_intrinsic_jets G H K hQ μ u jet hzero hi hc hs
  have hsplit0 (x : Fin N → ℝ) : u x = near K x + far K x := by
    rw [congrFun hrep.1 x]
    exact intrinsic_source_near_far_split G H μ u jet hzero hi hc hs ν hν
      K.locallyIntegrable K.smooth_off_zero hε x
  have hsplit1 (i : Fin q) (x : Fin N → ℝ) :
      jet [i.succ] x = near (fieldDerivative (H.fields i.succ) K) x +
        far (fieldDerivative (H.fields i.succ) K) x := by
    rw [congrFun (hrep.2 i) x]
    have hKi := H.horizontalKernel_locallyIntegrable G i (K.smooth_off_zero.of_le (by simp))
      K.homogeneous (by linarith)
    exact intrinsic_source_near_far_split G H μ u jet hzero hi hc hs ν hν hKi
      (fundamental_horizontal_type_one G H K i).smooth hε x
  have hglobal0 : normG u = normA u :=
    boundedHolderNorm_global_eq_of_controlNorm Hc (A := A) isOpen_ball hsu hsuA
  have hglobal1 (i : Fin q) : normG (jet [i.succ]) = normA (jet [i.succ]) :=
    boundedHolderNorm_global_eq_of_controlNorm Hc (A := A) isOpen_ball
      (hs _ (hw1 i)) (hsupport _ (hw1 i))
  have hz : normA u ≤ normA (near K) + normG (far K) := by
    have he := H2.boundedHolderNorm_congr (δ := α) (G := A) (fun x _ => hsplit0 x)
    calc
      _ = normA (fun x => near K x + far K x) := he
      _ ≤ normA (near K) + normA (far K) := H2.boundedHolderNorm_add_le
      _ ≤ _ := add_le_add le_rfl (H2.boundedHolderNorm_restrict (subset_univ A))
  have hj (i : Fin q) : normA (jet [i.succ]) ≤
      normA (near (fieldDerivative (H.fields i.succ) K)) +
        normG (far (fieldDerivative (H.fields i.succ) K)) := by
    have he := H2.boundedHolderNorm_congr (δ := α) (G := A) (fun x _ => hsplit1 i x)
    calc
      _ = normA (fun x => near (fieldDerivative (H.fields i.succ) K) x +
          far (fieldDerivative (H.fields i.succ) K) x) := he
      _ ≤ normA (near (fieldDerivative (H.fields i.succ) K)) +
          normA (far (fieldDerivative (H.fields i.succ) K)) := H2.boundedHolderNorm_add_le
      _ ≤ _ := add_le_add le_rfl (H2.boundedHolderNorm_restrict (subset_univ A))
  change normG u + (∑ i : Fin q, normG (jet [i.succ])) ≤ _
  rw [hglobal0]
  simp only [hglobal1]
  have hh := add_le_add hz (Finset.sum_le_sum (s := Finset.univ) (fun i _ => hj i))
  have he : normA (near K) + normG (far K) +
      (∑ i : Fin q, (normA (near (fieldDerivative (H.fields i.succ) K)) +
        normG (far (fieldDerivative (H.fields i.succ) K)))) =
      (normA (near K) + ∑ i : Fin q, normA (near (fieldDerivative (H.fields i.succ) K))) +
      (normG (far K) + ∑ i : Fin q, normG (far (fieldDerivative (H.fields i.succ) K))) := by
    rw [Finset.sum_add_distrib]
    ac_rfl
  exact (hh.trans_eq he).trans (add_le_add hn hf')

end RothschildStein.H3
