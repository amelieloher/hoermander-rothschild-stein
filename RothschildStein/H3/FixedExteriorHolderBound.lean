-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.ExteriorWordBounds
public import RothschildStein.H3.CompactConvolutionHolder
public import RothschildStein.H3.InterpolationCutoffProfile
public import RothschildStein.H1.Standing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal BigOperators
namespace RothschildStein.H3

/-- At one fixed scale the actual exterior homogeneous kernel
has a global convolution Hölder bound by the compact source mass.
Every field bound is instantiated from the prescribed homogeneous frame. -/
theorem fixed_exterior_holder_bound_of_controlNorm {N q : ℕ} (G : HomogeneousGroup N)
    (H : H1.StandingHypotheses G q)
    (Hc : G2.ControlNormConclusion G driftWeight H.fields)
    (ν : G2.HomogeneousNorm G) (hν : ν.Smooth)
    {F : (Fin N → ℝ) → ℝ} (hF : ContDiffOn ℝ (⊤ : ℕ∞) F {0}ᶜ)
    {γ : ℝ} (hγ : γ ≤ 0)
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 → F (G.dilate t x) = t ^ γ * F x)
    {α : ℝ≥0} (hα1 : (α : ℝ) ≤ 1) :
    let metric : MetricSpace (ControlCarrier N) :=
      gaugeMetric G Hc.norm Hc.constant_one Hc.symmetric
    ∃ C : ℝ, 0 < C ∧ ∀ u : (Fin N → ℝ) → ℝ,
      Continuous u → HasCompactSupport u →
      @H2.boundedHolderNorm (ControlCarrier N) metric α univ
        (fun x => G2.groupConvolution G u
          (exteriorCutoffKernel ν interpolationCutoffProfile F (1 / 2)) x) ≤
        ENNReal.ofReal (C * ∫ y, |u y|) := by
  classical
  let metric : MetricSpace (ControlCarrier N) :=
    gaugeMetric G Hc.norm Hc.constant_one Hc.symmetric
  have hfields (i : Fin (q + 1)) :
      G2.IsHomogeneousField G (H.fields i) ((driftWeight i : ℕ) : ℝ) := by
    by_cases hi : i = 0 <;> simpa [driftWeight, hi] using H.homogeneous i
  have hdegree (I : List (Fin (q + 1))) : γ - (wordWeight driftWeight I : ℝ) ≤ 0 := by
    have hw : (0 : ℝ) ≤ (wordWeight driftWeight I : ℝ) := by positivity
    linarith
  have hbounds (I : List (Fin (q + 1))) := exteriorCutoffKernel_word_bound driftWeight
    H.fields (H.fields_smooth G) hfields ν.gauge hν interpolationCutoffProfile_smooth
    (fun _ ht => interpolationCutoffProfile_one ht) (fun _ ht => interpolationCutoffProfile_zero ht)
    hF hhom I (hdegree I)
  choose A hA hbound using hbounds
  let D := fun I => A I * (1 / 2 : ℝ) ^ (γ - (wordWeight driftWeight I : ℝ))
  have hD (I : List (Fin (q + 1))) : 0 ≤ D I := mul_nonneg (hA I) (Real.rpow_nonneg (by norm_num) _)
  let M := D [] + (∑ i : Fin q, D [i.succ]) + D [0] + 1
  have hsum : 0 ≤ ∑ i : Fin q, D [i.succ] := Finset.sum_nonneg (fun i _ => hD _)
  have hM : 0 < M := by dsimp [M]; linarith [hD [], hD [0]]
  have hDM : D [] ≤ M := by dsimp [M]; linarith [hD [0]]
  have hSM : (∑ i : Fin q, D [i.succ]) ≤ M := by dsimp [M]; linarith [hD [], hD [0]]
  have h0M : D [0] ≤ M := by dsimp [M]; linarith [hD []]
  refine ⟨3 * M, by positivity, ?_⟩
  intro u hu hsu
  have hs := contDiff_kernel_exterior_cutoff ν.gauge hν interpolationCutoffProfile_smooth
    (fun _ ht => interpolationCutoffProfile_one ht) hF (by norm_num : 0 < (1 / 2 : ℝ))
  have hk : ∀ x, |exteriorCutoffKernel ν interpolationCutoffProfile F (1 / 2) x| ≤ M :=
    fun x => (hbound [] (1 / 2) (by norm_num) x).trans hDM
  have hfirst : ∀ x, ∀ i : Fin q,
      |fderiv ℝ (exteriorCutoffKernel ν interpolationCutoffProfile F (1 / 2)) x
        (H.fields i.succ x)| ≤ D [i.succ] := fun x i => hbound [i.succ] (1 / 2) (by norm_num) x
  have hdrift : ∀ x,
      |fderiv ℝ (exteriorCutoffKernel ν interpolationCutoffProfile F (1 / 2)) x
        (H.fields 0 x)| ≤ D [0] := fun x => hbound [0] (1 / 2) (by norm_num) x
  exact groupConvolution_holderNorm_of_field_bounds G Hc hu hsu (hs.of_le (by simp))
    hM.le hk hfirst hdrift hSM h0M hα1

end RothschildStein.H3
