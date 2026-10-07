-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.RightExteriorOperatorBounds
public import RothschildStein.H3.CompactConvolutionHolder

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal BigOperators
namespace RothschildStein.H3

/-- The exterior part of the right sum-of-squares kernel has a global
convolution Hölder bound with a common inverse scale, under the stated
kernel and global control-distance hypotheses. -/
theorem far_convolution_holder_scale_of_controlNorm {N q : ℕ} (G : HomogeneousGroup N)
    (H : H1.StandingHypotheses G q)
    (Hc : G2.ControlNormConclusion G driftWeight H.fields)
    {ν F : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (hsν : ContDiffOn ℝ (⊤ : ℕ∞) ν {0}ᶜ)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hone : ∀ t : ℝ, t ≤ 1 / 2 → φ t = 1)
    (hzero : ∀ t : ℝ, 1 ≤ t → φ t = 0)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F {0}ᶜ) {γ : ℝ} (hγ : γ ≤ 0)
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 → F (G.dilate t x) = t ^ γ * F x)
    {α : ℝ≥0} (hα1 : (α : ℝ) ≤ 1) :
    let metric : MetricSpace (ControlCarrier N) :=
      gaugeMetric G Hc.norm Hc.constant_one Hc.symmetric
    ∃ C : ℝ, 0 < C ∧ ∀ u : (Fin N → ℝ) → ℝ,
      Continuous u → HasCompactSupport u → ∀ ε : ℝ, 0 < ε → ε < 1 →
      @H2.boundedHolderNorm (ControlCarrier N) metric α univ
        (fun x => G2.groupConvolution G u
          (sumSquaresWithDrift (fun i => G2.rightField G (H.fields i 0))
            (exteriorCutoffKernel ν φ F ε)) x) ≤
        ENNReal.ofReal (C * ε ^ (γ - 4) * ∫ y, |u y|) := by
  let metric : MetricSpace (ControlCarrier N) :=
    gaugeMetric G Hc.norm Hc.constant_one Hc.symmetric
  obtain ⟨A, B, hA, hB, hk⟩ :=
    exists_right_exterior_operator_bounds G H hν hsν hφ hone hzero hF hγ hhom
  let k := A + (q : ℝ) * B + B + 1
  have hq : 0 ≤ (q : ℝ) := Nat.cast_nonneg q
  have hqB : 0 ≤ (q : ℝ) * B := mul_nonneg hq hB
  have hkpos : 0 < k := by dsimp [k]; linarith
  have hAk : A ≤ k := by dsimp [k]; linarith
  have hBk : B ≤ k := by dsimp [k]; linarith
  have hqBk : (q : ℝ) * B ≤ k := by dsimp [k]; linarith
  refine ⟨3 * k, mul_pos (by norm_num) hkpos, ?_⟩
  intro u hu hsu ε hε hε1
  let P := sumSquaresWithDrift (fun i => G2.rightField G (H.fields i 0))
    (exteriorCutoffKernel ν φ F ε)
  let M := k * ε ^ (γ - 4)
  have hp : 0 ≤ ε ^ (γ - 4) := Real.rpow_nonneg hε.le _
  have hM : 0 ≤ M := mul_nonneg hkpos.le hp
  have hkernel := hk ε hε hε1
  have hbound : ∀ x, |P x| ≤ M := fun x => (hkernel.2.1 x).trans
    (mul_le_mul_of_nonneg_right hAk hp)
  have hfirst : ∀ x, ∀ i : Fin q,
      |fderiv ℝ P x (H.fields i.succ x)| ≤ B * ε ^ (γ - 4) := fun x i => hkernel.2.2 i.succ x
  have hdrift : ∀ x, |fderiv ℝ P x (H.fields 0 x)| ≤ B * ε ^ (γ - 4) := fun x => hkernel.2.2 0 x
  have hsum : (∑ _i : Fin q, B * ε ^ (γ - 4)) ≤ M := by
    have he : (∑ _i : Fin q, B * ε ^ (γ - 4)) = (q : ℝ) * B * ε ^ (γ - 4) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    rw [he]
    exact mul_le_mul_of_nonneg_right hqBk hp
  have hb := groupConvolution_holderNorm_of_field_bounds G Hc hu hsu
    (hkernel.1.of_le (by simp)) hM hbound hfirst hdrift hsum
    (mul_le_mul_of_nonneg_right hBk hp) hα1
  have he : 3 * M * (∫ y, |u y|) = (3 * k) * ε ^ (γ - 4) * (∫ y, |u y|) := by dsimp [M]; ring
  rw [he] at hb
  exact hb

end RothschildStein.H3
