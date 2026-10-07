-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.FixedExteriorHolderBound
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

/-- The exterior fundamental kernel and all its horizontal
first kernels have one global Hölder convolution bound at fixed scale.
The potential itself is not required to have compact support. -/
theorem fundamental_fixed_exterior_holder_bounds_of_controlNorm {N q : ℕ} (G : HomogeneousGroup N)
    (H : H1.StandingHypotheses G q) (K : H1.FundamentalKernel G H)
    (Hc : G2.ControlNormConclusion G driftWeight H.fields)
    (hQ : 2 < (G.homogeneousDimension : ℝ))
    (ν : G2.HomogeneousNorm G) (hν : ν.Smooth)
    {α : ℝ≥0} (hα1 : (α : ℝ) ≤ 1) :
    let metric : MetricSpace (ControlCarrier N) :=
      gaugeMetric G Hc.norm Hc.constant_one Hc.symmetric
    ∃ C : ℝ, 0 < C ∧ ∀ u : (Fin N → ℝ) → ℝ,
      Continuous u → HasCompactSupport u →
      @H2.boundedHolderNorm (ControlCarrier N) metric α univ
        (fun x => G2.groupConvolution G u
          (exteriorCutoffKernel ν interpolationCutoffProfile K (1 / 2)) x) +
      (∑ i : Fin q, @H2.boundedHolderNorm (ControlCarrier N) metric α univ
        (fun x => G2.groupConvolution G u
          (exteriorCutoffKernel ν interpolationCutoffProfile
            (fieldDerivative (H.fields i.succ) K) (1 / 2)) x)) ≤
      ENNReal.ofReal (C * ∫ y, |u y|) := by
  classical
  let metric : MetricSpace (ControlCarrier N) :=
    gaugeMetric G Hc.norm Hc.constant_one Hc.symmetric
  obtain ⟨C₀, hC₀, hb₀⟩ := fixed_exterior_holder_bound_of_controlNorm G H Hc ν hν
    K.smooth_off_zero (by linarith : 2 - (G.homogeneousDimension : ℝ) ≤ 0) K.homogeneous hα1
  have hfirst (i : Fin q) := fixed_exterior_holder_bound_of_controlNorm G H Hc ν hν
    (fundamental_horizontal_type_one G H K i).smooth
    (by linarith : 1 - (G.homogeneousDimension : ℝ) ≤ 0)
    (fundamental_horizontal_type_one G H K i).homogeneous hα1
  choose B hB hb using hfirst
  let C := C₀ + (∑ i : Fin q, B i) + 1
  have hsum : 0 ≤ ∑ i : Fin q, B i := Finset.sum_nonneg (fun i _ => (hB i).le)
  refine ⟨C, by dsimp [C]; linarith, ?_⟩
  intro u hu hsu
  have hmass : 0 ≤ ∫ y, |u y| := integral_nonneg (fun y => abs_nonneg (u y))
  have hz := hb₀ u hu hsu
  have hi (i : Fin q) := hb i u hu hsu
  have hh := add_le_add hz (Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i))
  have he : ENNReal.ofReal (C₀ * (∫ y, |u y|)) +
      (∑ i : Fin q, ENNReal.ofReal (B i * (∫ y, |u y|))) =
      ENNReal.ofReal ((C₀ + ∑ i : Fin q, B i) * (∫ y, |u y|)) := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hB i).le hmass),
      ← ENNReal.ofReal_add (mul_nonneg hC₀.le hmass)
        (Finset.sum_nonneg (fun i _ => mul_nonneg (hB i).le hmass))]
    congr 1
    rw [← Finset.sum_mul]
    ring
  apply (hh.trans_eq he).trans
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right (show C₀ + ∑ i : Fin q, B i ≤ C by dsimp [C]; linarith) hmass

end RothschildStein.H3
