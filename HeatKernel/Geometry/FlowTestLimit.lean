-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Geometry.FlowDifferenceQuotient
public import RothschildStein.S.FlowTestIntegralLimit

/-! Convergence of compact test-function difference quotients along complete horizontal flows. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory RothschildStein Filter TopologicalSpace
open scoped Topology
namespace HeatKernel

/-- The horizontal flow is jointly continuous in its starting point and time. -/
theorem continuous_horizontalFlow {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N)
    (b : Fin q → ℝ) : Continuous (fun p : (Fin N → ℝ) × ℝ => horizontalFlow G hq b p.1 p.2) := by
  change Continuous (fun p : (Fin N → ℝ) × ℝ => G.mul p.1 (G2.leftExponential G (horizontalTangent hq b) p.2))
  have hγ : Continuous (fun p : (Fin N → ℝ) × ℝ => G2.leftExponential G (horizontalTangent hq b) p.2) :=
    (G2.continuous_leftExponential G (horizontalTangent hq b)).comp continuous_snd
  apply continuous_pi
  intro j
  exact (MvPolynomial.continuous_eval (p := G.productPolynomial j)).comp
    (continuous_pi fun i => Sum.casesOn i
      (fun k => (continuous_apply k).comp continuous_fst)
      (fun k => (continuous_apply k).comp hγ))

/-- Compact smooth test quotients converge under integration against any continuous function. -/
theorem tendsto_integral_horizontalFlow_testQuotient {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q ≤ N) (b : Fin q → ℝ) {f ψ : (Fin N → ℝ) → ℝ}
    (hf : Continuous f) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hcψ : HasCompactSupport ψ) :
    Tendsto (fun h => ∫ x, f x * ((ψ (horizontalFlow G hq b x h) - ψ x) / h))
      (𝓝[≠] (0 : ℝ))
      (𝓝 (∫ x, f x * fieldDerivative (G2.leftField G (horizontalTangent hq b)) ψ x)) := by
  let K : Compacts (Fin N → ℝ) := ⟨tsupport ψ, hcψ⟩
  let Φ := fun p : (Fin N → ℝ) × ℝ => horizontalFlow G hq b p.1 p.2
  have hΦ : Continuous Φ := continuous_horizontalFlow G hq b
  let C : Compacts (Fin N → ℝ) :=
    ⟨Φ '' ((K : Set (Fin N → ℝ)) ×ˢ Icc (-1 : ℝ) 1),
      (K.isCompact.prod isCompact_Icc).image hΦ⟩
  have hKC : (K : Set (Fin N → ℝ)) ⊆ C := by
    intro x hx
    exact ⟨(x, 0), ⟨hx, by norm_num⟩, horizontalFlow_zero G hq b x⟩
  have hsol : ∀ x ∈ (univ : Set (Fin N → ℝ)), Φ (x, 0) = x ∧
      ∀ t ∈ Ioo (-2 : ℝ) 2,
        HasDerivAt (fun v => Φ (x, v)) (G2.leftField G (horizontalTangent hq b) (Φ (x, t))) t ∧
        Φ (x, t) ∈ (⊤ : Opens (Fin N → ℝ)) := by
    intro x _
    refine ⟨horizontalFlow_zero G hq b x, fun t _ => ⟨?_, mem_univ _⟩⟩
    exact G2.leftExponential_translated_integralCurve G (horizontalTangent hq b) x t
  have H := S.tendsto_integral_flow_test_quotient ⊤ K C (subset_univ _) (subset_univ _) hKC
    (G2.leftField G (horizontalTangent hq b)) (G2.contDiff_leftField G _).contDiffOn hf.continuousOn
    (U := univ) (V := univ) isOpen_univ Subset.rfl (subset_univ _) (subset_univ _)
    (τ := 2) (δ := 1) (by norm_num) (by norm_num) Φ hΦ.continuousOn hsol
    (fun x hx t ht => ⟨(x, t), ⟨hx, ht⟩, rfl⟩) ψ hψ Subset.rfl
  simpa only [Measure.restrict_univ] using H

/-- Backward-step difference quotients of a continuous function converge in every compact
smooth test pairing to the negative action of the horizontal field on the test. -/
theorem tendsto_integral_horizontalFlow_differenceQuotient_test {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q ≤ N) (b : Fin q → ℝ) {f ψ : (Fin N → ℝ) → ℝ}
    (hf : Continuous f) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hcψ : HasCompactSupport ψ) :
    Tendsto (fun h => ∫ x, ((f (horizontalFlow G hq b x (-h)) - f x) / (-h)) * ψ x)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (-(∫ x, f x * fieldDerivative (G2.leftField G (horizontalTangent hq b)) ψ x))) := by
  have hg : Integrable (fun x => f x * ψ x) :=
    (hf.mul hψ.continuous).integrable_of_hasCompactSupport hcψ.mul_left
  have he : ∀ h : ℝ, -(∫ x, f x * ((ψ (horizontalFlow G hq b x h) - ψ x) / h)) =
      ∫ x, ((f (horizontalFlow G hq b x (-h)) - f x) / (-h)) * ψ x := by
    intro h
    have hflow : Continuous (fun x => horizontalFlow G hq b x (-h)) := by
      change Continuous (fun x => G.mul x (G2.leftExponential G (horizontalTangent hq b) (-h)))
      exact (G2.contDiff_rightTranslation G _).continuous
    have hi : Integrable (fun x => f (horizontalFlow G hq b x (-h)) * ψ x) :=
      ((hf.comp hflow).mul hψ.continuous).integrable_of_hasCompactSupport hcψ.mul_left
    simpa only [neg_neg, div_neg, mul_div_assoc, integral_neg] using
      integral_horizontalFlow_differenceQuotient G hq b (-h) f ψ hi hg
  exact (tendsto_integral_horizontalFlow_testQuotient G hq b hf hψ hcψ).neg.congr he

end HeatKernel
