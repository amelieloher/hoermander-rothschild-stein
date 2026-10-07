-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.CenteredScaledGroupSetting
public import RothschildStein.H3.RadialCutoffGeometry
public import RothschildStein.H3.CutoffKernelMeasurability
public import RothschildStein.G2.ConvolutionSubstitution
public import RothschildStein.H2.IntegralDefs
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import RothschildStein.H2.FractionalHolderNorm
public import RothschildStein.H2.KernelRestriction
public import RothschildStein.H2.HolderOperations

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal NNReal
namespace RothschildStein.H3
open G2
variable {N : ℕ} {G : HomogeneousGroup N}

/-- near part. A supported cutoff-kernel certificate gives
its actual convolution's Hölder bound on fixed buffered balls. The
integration radius is fixed independently of the cutoff's smaller scale. -/
theorem centered_cutoff_convolution_holder_of_kernelClass
    (ν : HomogeneousNorm G) (h1 : ν.c = 1) (hsym : ν.Symmetric)
    (z : ControlCarrier N) {r : ℝ} (hr : 0 < r)
    {T χ : (Fin N → ℝ) → ℝ} {v A S R : ℝ}
    (hR : 0 < R) (hRr : R ≤ 9 * r)
    (hχsupp : ∀ w, R ≤ ν w → χ w = 0)
    (hK : let metric : MetricSpace (ControlCarrier N) := gaugeMetric G ν h1 hsym
      @H2.KernelClass (ControlCarrier N) metric inferInstance volume univ 1 v A S
        (fun x y => cutoffGroupKernel G χ T x y))
    {α : ℝ≥0} (hα : 0 < α) (hα1 : (α : ℝ) ≤ 1) (hαv : (α : ℝ) < v)
    {u : (Fin N → ℝ) → ℝ} (hu : MemLp u ∞ volume)
    (hsu : tsupport u ⊆ gaugeBall G ν z r) :
    let metric : MetricSpace (ControlCarrier N) := gaugeMetric G ν h1 hsym
    @H2.boundedHolderNorm (ControlCarrier N) metric α (ball z r)
      (fun x => groupConvolution G u (fun w => χ w * T w) x) ≤
      ENNReal.ofReal (H2.fractionalHolderConstant
        ((2 : ℝ) ^ G.homogeneousDimension) (3 * r) R α v *
          (A + S) * lpNorm u ∞ volume) := by
  let metric : MetricSpace (ControlCarrier N) := gaugeMetric G ν h1 hsym
  let D := centeredScaledGroupSetting G ν h1 hsym z r hr
  let K : ControlCarrier N → ControlCarrier N → ℝ := cutoffGroupKernel G χ T
  have hlocal : H2.SupportedKernel D D.Ω₀ D.Ω₁ 1 v A S R K := by
    refine ⟨D.open₀.measurableSet, D.sub₀₁, subset_rfl, hR, ?_,
      hK.restrict D.open₁.measurableSet (subset_univ _), ?_⟩
    · change R ≤ 3 * (3 * r)
      linarith
    · intro x _ y _ hxy
      change R ≤ ν (G.mul (G.inv y) x) at hxy
      change χ (G.mul (G.inv y) x) * T (G.mul (G.inv y) x) = 0
      rw [hχsupp _ hxy, MulZeroClass.zero_mul]
  have hfb : ∀ᵐ y ∂volume.restrict D.Ω₁, |u y| ≤ lpNorm u ∞ volume :=
    ae_restrict_of_ae (by simpa only [Real.norm_eq_abs] using ae_le_lpNorm_exponent_top hu)
  have hf : AEStronglyMeasurable u (volume.restrict D.Ω₁) :=
    hu.aestronglyMeasurable.mono_measure Measure.restrict_le_self
  have hb := hlocal.fractional_holder_norm_le hα hα1 hαv hf lpNorm_nonneg hfb
  have he : EqOn (fun x : ControlCarrier N => groupConvolution G u (fun w => χ w * T w) x)
      (H2.fractionalIntegral volume D.Ω₁ K u) D.Ω₀ := by
    intro x _hx
    change groupConvolution G u (fun w => χ w * T w) (x : Fin N → ℝ) = _
    rw [groupConvolution_eq_integral]
    unfold H2.fractionalIntegral
    rw [← integral_indicator D.open₁.measurableSet]
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : y ∈ D.Ω₁
    · rw [indicator_of_mem hy]
      change u y * (χ (G.mul (G.inv y) x) * T (G.mul (G.inv y) x)) =
        (χ (G.mul (G.inv y) x) * T (G.mul (G.inv y) x)) * u y
      exact mul_comm _ _
    · rw [indicator_of_notMem hy]
      have hyu : y ∉ tsupport u := by
        intro hs
        have ht : @dist (ControlCarrier N) metric.toDist y z < r := hsu hs
        apply hy
        change @dist (ControlCarrier N) metric.toDist y z < 19 * r
        linarith
      rw [image_eq_zero_of_notMem_tsupport hyu, MulZeroClass.zero_mul]
  change H2.boundedHolderNorm α D.Ω₀
      (fun x : ControlCarrier N => groupConvolution G u (fun w => χ w * T w) x) ≤
    ENNReal.ofReal (H2.fractionalHolderConstant D.C_D D.κ R α v *
      (A + S) * lpNorm u ∞ volume)
  rw [H2.boundedHolderNorm_congr he]
  exact hb

end RothschildStein.H3
