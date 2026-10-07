-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.FarConvolutionScale
public import RothschildStein.H3.FundamentalPositiveTypes
public import RothschildStein.H3.InterpolationCutoffProfile

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal BigOperators
namespace RothschildStein.H3

/-- far part. The fundamental kernel and its horizontal first
kernels share the inverse scale epsilon^(-3-Q) after the right operator.
The constant is fixed before the compact source and the scale. -/
theorem fundamental_far_convolution_bounds_of_controlNorm {N q : ℕ} (G : HomogeneousGroup N)
    (H : H1.StandingHypotheses G q) (K : H1.FundamentalKernel G H)
    (Hc : G2.ControlNormConclusion G driftWeight H.fields)
    (hQ : 2 < (G.homogeneousDimension : ℝ))
    (ν : G2.HomogeneousNorm G) (hν : ν.Smooth)
    {α : ℝ≥0} (hα1 : (α : ℝ) ≤ 1) :
    let metric : MetricSpace (ControlCarrier N) :=
      gaugeMetric G Hc.norm Hc.constant_one Hc.symmetric
    let R := sumSquaresWithDrift (fun i => G2.rightField G (H.fields i 0))
    ∃ C : ℝ, 0 < C ∧ ∀ u : (Fin N → ℝ) → ℝ,
      Continuous u → HasCompactSupport u → ∀ ε : ℝ, 0 < ε → ε < 1 →
      @H2.boundedHolderNorm (ControlCarrier N) metric α univ
        (fun x => G2.groupConvolution G u
          (R (exteriorCutoffKernel ν interpolationCutoffProfile K ε)) x) +
      (∑ i : Fin q, @H2.boundedHolderNorm (ControlCarrier N) metric α univ
        (fun x => G2.groupConvolution G u
          (R (exteriorCutoffKernel ν interpolationCutoffProfile
            (fieldDerivative (H.fields i.succ) K) ε)) x)) ≤
      ENNReal.ofReal (C * ε ^ (-3 - (G.homogeneousDimension : ℝ)) * ∫ y, |u y|) := by
  classical
  let metric : MetricSpace (ControlCarrier N) :=
    gaugeMetric G Hc.norm Hc.constant_one Hc.symmetric
  obtain ⟨C₀, hC₀, hb₀⟩ := far_convolution_holder_scale_of_controlNorm G H Hc ν.gauge hν
    interpolationCutoffProfile_smooth (fun _ ht => interpolationCutoffProfile_one ht)
    (fun _ ht => interpolationCutoffProfile_zero ht) K.smooth_off_zero
    (by linarith : 2 - (G.homogeneousDimension : ℝ) ≤ 0) K.homogeneous hα1
  have hfirst (i : Fin q) := far_convolution_holder_scale_of_controlNorm G H Hc ν.gauge hν
    interpolationCutoffProfile_smooth (fun _ ht => interpolationCutoffProfile_one ht)
    (fun _ ht => interpolationCutoffProfile_zero ht)
    (fundamental_horizontal_type_one G H K i).smooth
    (by linarith : 1 - (G.homogeneousDimension : ℝ) ≤ 0)
    (fundamental_horizontal_type_one G H K i).homogeneous hα1
  choose B hB hb using hfirst
  let C := C₀ + (∑ i : Fin q, B i) + 1
  have hsum : 0 ≤ ∑ i : Fin q, B i := Finset.sum_nonneg (fun i _ => (hB i).le)
  refine ⟨C, by dsimp [C]; linarith, ?_⟩
  intro u hu hsu ε hε hε1
  have hmass : 0 ≤ ∫ y, |u y| := integral_nonneg (fun y => abs_nonneg (u y))
  let p := ε ^ (-3 - (G.homogeneousDimension : ℝ))
  have hp : 0 ≤ p := Real.rpow_nonneg hε.le _
  have hz := hb₀ u hu hsu ε hε hε1
  have he2 : 2 - (G.homogeneousDimension : ℝ) - 4 = -2 - G.homogeneousDimension := by ring
  have he1 : 1 - (G.homogeneousDimension : ℝ) - 4 = -3 - G.homogeneousDimension := by ring
  rw [he2] at hz
  have hpower : ε ^ (-2 - (G.homogeneousDimension : ℝ)) ≤ p :=
    Real.rpow_le_rpow_of_exponent_ge hε hε1.le (by linarith)
  have hz' := hz.trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpower hC₀.le) hmass))
  have hi (i : Fin q) := hb i u hu hsu ε hε hε1
  simp only [he1] at hi
  have hh := add_le_add hz' (Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i))
  have he : ENNReal.ofReal (C₀ * p * (∫ y, |u y|)) +
      (∑ i : Fin q, ENNReal.ofReal (B i * p * (∫ y, |u y|))) =
      ENNReal.ofReal ((C₀ + ∑ i : Fin q, B i) * p * (∫ y, |u y|)) := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (mul_nonneg (hB i).le hp) hmass),
      ← ENNReal.ofReal_add (mul_nonneg (mul_nonneg hC₀.le hp) hmass)
        (Finset.sum_nonneg (fun i _ => mul_nonneg (mul_nonneg (hB i).le hp) hmass))]
    congr 1
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    ring
  apply (hh.trans_eq he).trans
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (show C₀ + ∑ i : Fin q, B i ≤ C by dsimp [C]; linarith) hp) hmass

end RothschildStein.H3
