-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.IntrinsicConvolutionCurve
public import RothschildStein.S.IntrinsicCurveExistence
public import RothschildStein.S.IntrinsicUniqueness
public import RothschildStein.H3.IntrinsicLocalization
public import RothschildStein.G2.ConvolutionSmooth
public import Mathlib.Analysis.Normed.Group.Bounded

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology
namespace RothschildStein.H3
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Group convolution preserves bounded continuous intrinsic
first derivatives, in the fixed curve-based predicate. -/
theorem hasIntrinsicDeriv_convolution_of_bounded
    (X : (Fin N → ℝ) → (Fin N → ℝ)) (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (hleft : G2.IsLeftInvariantField G X)
    {ψ f g : (Fin N → ℝ) → ℝ} (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ)
    (hf : Continuous f) (hg : Continuous g) (hfg : hasIntrinsicDeriv ⊤ X f g)
    {Mf Mg : ℝ} (hMf : ∀ z, |f z| ≤ Mf) (hMg : ∀ z, |g z| ≤ Mg) :
    hasIntrinsicDeriv ⊤ X (G2.groupConvolution G ψ f) (G2.groupConvolution G ψ g) := by
  intro x _
  refine ⟨S.exists_intrinsic_integral_curve ⊤ X hX.contDiffOn (mem_univ x), ?_⟩
  intro γ hzero hγ _
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hγ
  have hcurve : IsIntegralCurveOn γ (fun _ => X) (ball (0 : ℝ) r) :=
    fun t ht => (hsub ht).hasDerivWithinAt
  have hd := hasDerivAt_convolution_curve_of_intrinsic G X hX hleft hψ hcψ hf hg
    hfg hMf hMg isOpen_ball hcurve (mem_ball_self hr)
  simpa only [hzero] using hd

/-- Compactly supported continuous functions with compactly
supported continuous intrinsic derivative commute with convolution by
a compact continuous kernel, without any scalar smoothness premise. -/
theorem hasIntrinsicDeriv_convolution_of_compact
    (X : (Fin N → ℝ) → (Fin N → ℝ)) (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (hleft : G2.IsLeftInvariantField G X)
    {ψ f g : (Fin N → ℝ) → ℝ} (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ)
    (hf : Continuous f) (hcf : HasCompactSupport f)
    (hg : Continuous g) (hcg : HasCompactSupport g) (hfg : hasIntrinsicDeriv ⊤ X f g) :
    hasIntrinsicDeriv ⊤ X (G2.groupConvolution G ψ f) (G2.groupConvolution G ψ g) := by
  obtain ⟨Mf, hMf⟩ := hcf.exists_bound_of_continuous hf
  obtain ⟨Mg, hMg⟩ := hcg.exists_bound_of_continuous hg
  exact hasIntrinsicDeriv_convolution_of_bounded G X hX hleft hψ hcψ hf hg hfg
    (fun z => by simpa only [Real.norm_eq_abs] using hMf z)
    (fun z => by simpa only [Real.norm_eq_abs] using hMg z)

/-- A smooth compact convolution kernel commutes pointwise
with the actual invariant field derivative of a compact continuous
intrinsic input. This gives the mollification identity for ψ=φε. -/
theorem fieldDerivative_convolution_of_compact_intrinsic
    (X : (Fin N → ℝ) → (Fin N → ℝ)) (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (hleft : G2.IsLeftInvariantField G X)
    {ψ f g : (Fin N → ℝ) → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hcψ : HasCompactSupport ψ) (hf : Continuous f) (hcf : HasCompactSupport f)
    (hg : Continuous g) (hcg : HasCompactSupport g) (hfg : hasIntrinsicDeriv ⊤ X f g) :
    fieldDerivative X (G2.groupConvolution G ψ f) = G2.groupConvolution G ψ g := by
  have hconv := hasIntrinsicDeriv_convolution_of_compact G X hX hleft hψ.continuous
    hcψ hf hcf hg hcg hfg
  have hsm := G2.contDiff_groupConvolution_left G hψ hcψ hf.locallyIntegrable
  have hclass := intrinsicDeriv_of_differentiable ⊤ X hX.contDiffOn
    (hsm.differentiable (by simp))
  funext x
  exact S.hasIntrinsicDeriv_unique ⊤ X hclass hconv (mem_univ x)

end RothschildStein.H3
