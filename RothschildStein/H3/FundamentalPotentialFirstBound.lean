-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.HomogeneousFieldKernelRegularity
public import RothschildStein.H3.FundamentalExteriorHolderBound
public import RothschildStein.H3.FundamentalNearBounds
public import RothschildStein.H3.NearFarConvolution
public import RothschildStein.H3.IntrinsicJetSourceData

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal NNReal BigOperators
namespace RothschildStein.H3

/-- The actual fundamental potential and its first kernel
convolutions have one local full Hölder bound by the source supremum.
The compact support condition is imposed on the source. -/
theorem fundamental_potential_first_holder_bound_of_controlNorm {N q : ℕ} (G : HomogeneousGroup N)
    (H : H1.StandingHypotheses G q) (K : H1.FundamentalKernel G H)
    (Hc : G2.ControlNormConclusion G driftWeight H.fields)
    (hQ : 2 < (G.homogeneousDimension : ℝ))
    (ν : G2.HomogeneousNorm G) (hν : ν.Smooth)
    {α : ℝ≥0} (hα : 0 < α) (hα1 : (α : ℝ) < 1) {ρ : ℝ} (hρ : 0 < ρ) :
    let metric : MetricSpace (ControlCarrier N) :=
      gaugeMetric G Hc.norm Hc.constant_one Hc.symmetric
    ∃ C : ℝ, 0 < C ∧ ∀ z : ControlCarrier N, ∀ u : (Fin N → ℝ) → ℝ,
      Continuous u → HasCompactSupport u → tsupport u ⊆ G2.gaugeBall G Hc.norm z ρ →
      @H2.boundedHolderNorm (ControlCarrier N) metric α (ball z ρ)
        (fun x => G2.groupConvolution G u K x) +
        (∑ i : Fin q, @H2.boundedHolderNorm (ControlCarrier N) metric α (ball z ρ)
          (fun x => G2.groupConvolution G u (fieldDerivative (H.fields i.succ) K) x)) ≤
        ENNReal.ofReal (C * lpNorm u ∞ volume) := by
  classical
  let metric : MetricSpace (ControlCarrier N) :=
    gaugeMetric G Hc.norm Hc.constant_one Hc.symmetric
  obtain ⟨a, ha, hnear⟩ := fundamental_near_convolution_bounds_of_controlNorm G H K Hc hQ ν hν hα hα1 hρ
  obtain ⟨b, hb, hfar⟩ := fundamental_fixed_exterior_holder_bounds_of_controlNorm G H K Hc hQ ν hν hα1.le
  let p := (1 / 2 : ℝ) ^ ((1 - (α : ℝ)) / 2)
  let v := (volume (G2.gaugeBall G Hc.norm 0 ρ)).toReal
  let C := a * p + b * v + 1
  have hp : 0 < p := Real.rpow_pos_of_pos (by norm_num) _
  have hv : 0 ≤ v := ENNReal.toReal_nonneg
  have hC : 0 < C := by dsimp [C]; linarith [mul_pos ha hp, mul_nonneg hb.le hv]
  refine ⟨C, hC, ?_⟩
  intro z u hu hsu hsupport
  let A := ball z ρ
  let near := fun (T : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) => G2.groupConvolution G u
    (fun w => smoothQuasiballCutoff G ν 0 ((1 / 2) / 2) (1 / 2) w * T w) x
  let far := fun (T : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) => G2.groupConvolution G u
    (exteriorCutoffKernel ν interpolationCutoffProfile T (1 / 2)) x
  let full := fun (T : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) => G2.groupConvolution G u T x
  let normA := fun f : (Fin N → ℝ) → ℝ => @H2.boundedHolderNorm (ControlCarrier N) metric α A (fun x => f x)
  let normG := fun f : (Fin N → ℝ) → ℝ => @H2.boundedHolderNorm (ControlCarrier N) metric α univ (fun x => f x)
  have hn := hnear z u (hu.memLp_of_hasCompactSupport hsu) hsupport (1 / 2) (by norm_num) (by norm_num)
  have hf := hfar u hu hsu
  have hm := integral_abs_le_gaugeBall_mass G Hc.norm hρ hu hsu z hsupport
  have hs0 (x : Fin N → ℝ) : full K x = near K x + far K x :=
    groupConvolution_near_far_split G ν hν hu hsu K.locallyIntegrable K.smooth_off_zero (by norm_num) x
  have hs1 (i : Fin q) (x : Fin N → ℝ) :
      full (fieldDerivative (H.fields i.succ) K) x =
        near (fieldDerivative (H.fields i.succ) K) x + far (fieldDerivative (H.fields i.succ) K) x := by
    exact groupConvolution_near_far_split G ν hν hu hsu
      (H.horizontalKernel_locallyIntegrable G i (K.smooth_off_zero.of_le (by simp)) K.homogeneous (by linarith))
      (fundamental_horizontal_type_one G H K i).smooth (by norm_num) x
  have htriangle (T : (Fin N → ℝ) → ℝ) (hsplit : ∀ x, full T x = near T x + far T x) :
      normA (full T) ≤ normA (near T) + normG (far T) := by
    have he := H2.boundedHolderNorm_congr (δ := α) (G := A) (fun x _ => hsplit x)
    calc
      _ = normA (fun x => near T x + far T x) := he
      _ ≤ normA (near T) + normA (far T) := H2.boundedHolderNorm_add_le
      _ ≤ _ := add_le_add le_rfl (H2.boundedHolderNorm_restrict (subset_univ A))
  have ht := add_le_add (htriangle K hs0)
    (Finset.sum_le_sum (s := Finset.univ) (fun i _ => htriangle (fieldDerivative (H.fields i.succ) K) (hs1 i)))
  have hreorder : normA (near K) + normG (far K) +
      (∑ i : Fin q, (normA (near (fieldDerivative (H.fields i.succ) K)) + normG (far (fieldDerivative (H.fields i.succ) K)))) =
      (normA (near K) + ∑ i : Fin q, normA (near (fieldDerivative (H.fields i.succ) K))) +
      (normG (far K) + ∑ i : Fin q, normG (far (fieldDerivative (H.fields i.succ) K))) := by
    rw [Finset.sum_add_distrib]
    ring
  have ht' := ht.trans_eq hreorder
  have hf' : normG (far K) + (∑ i : Fin q, normG (far (fieldDerivative (H.fields i.succ) K))) ≤
      ENNReal.ofReal (b * v * lpNorm u ∞ volume) := by
    apply hf.trans
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ b * (v * lpNorm u ∞ volume) := mul_le_mul_of_nonneg_left hm hb.le
      _ = _ := by ring
  have hbnd := ht'.trans (add_le_add hn hf')
  rw [← ENNReal.ofReal_add (mul_nonneg (mul_nonneg ha.le hp.le) lpNorm_nonneg)
    (mul_nonneg (mul_nonneg hb.le hv) lpNorm_nonneg)] at hbnd
  exact hbnd.trans (ENNReal.ofReal_le_ofReal (by
    have hcoef : a * p + b * v ≤ C := by dsimp [C]; linarith
    have hh := mul_le_mul_of_nonneg_right hcoef (lpNorm_nonneg (f := u) (p := ∞) (μ := volume))
    nlinarith))

end RothschildStein.H3
