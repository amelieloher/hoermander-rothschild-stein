-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.FarKernelTransfer
public import RothschildStein.H3.ScaledControlHolder

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal NNReal BigOperators
namespace RothschildStein.H3
variable {N : ℕ} (G : HomogeneousGroup N)

/-- far part. The actual compact-source convolution inherits
 the kernel's global bound, with the source's actual absolute integral. -/
theorem groupConvolution_abs_le_source_mass
    {u F : (Fin N → ℝ) → ℝ} (hu : Continuous u) (hsu : HasCompactSupport u)
    (hF : Continuous F) {M : ℝ} (hbound : ∀ x, |F x| ≤ M) (x : Fin N → ℝ) :
    |G2.groupConvolution G u F x| ≤ M * ∫ y, |u y| := by
  have hi := groupConvolution_exists_compact_continuous_kernel G hu hsu hF x
  have huabs : Integrable (fun y => |u y|) volume := hu.abs.integrable_of_hasCompactSupport hsu.abs
  rw [G2.groupConvolution_eq_integral]
  calc
    _ ≤ ∫ y, |u y * F (G.mul (G.inv y) x)| := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun y => u y * F (G.mul (G.inv y) x))
    _ ≤ ∫ y, |u y| * M := integral_mono hi.norm (huabs.mul_const M) (fun y => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hbound _) (abs_nonneg _))
    _ = _ := by rw [integral_mul_const]; ring

/-- far part. A genuine global bounded kernel modulus
passes through compact-source convolution and gives the full Hölder norm.
This analytic helper does not assert the interpolation parent theorem. -/
theorem groupConvolution_holderNorm_of_kernel_modulus
    (ν : G2.HomogeneousNorm G) (h1 : ν.c = 1) (hsym : ν.Symmetric)
    {u F : (Fin N → ℝ) → ℝ} (hu : Continuous u) (hsu : HasCompactSupport u)
    (hF : Continuous F) {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ x, |F x| ≤ M)
    (hmod : ∀ x y, |F x - F y| ≤ M *
      (G2.gaugeDistance G ν x y + G2.gaugeDistance G ν x y ^ 2))
    {α : ℝ≥0} (hα1 : (α : ℝ) ≤ 1) :
    let metric : MetricSpace (ControlCarrier N) := gaugeMetric G ν h1 hsym
    @H2.boundedHolderNorm (ControlCarrier N) metric α univ
      (fun x => G2.groupConvolution G u F x) ≤
        ENNReal.ofReal (3 * M * ∫ y, |u y|) := by
  let metric : MetricSpace (ControlCarrier N) := gaugeMetric G ν h1 hsym
  let mass := ∫ y, |u y|
  have hmass : 0 ≤ mass := integral_nonneg (fun y => abs_nonneg (u y))
  have huabs : Integrable (fun y => |u y|) volume := hu.abs.integrable_of_hasCompactSupport hsu.abs
  have hex (x : Fin N → ℝ) := groupConvolution_exists_compact_continuous_kernel G hu hsu hF x
  have hn := scaled_cutoff_holderNorm_le (X := ControlCarrier N)
    (f := fun x : ControlCarrier N => G2.groupConvolution G u F x)
    (mul_nonneg hM hmass) (by norm_num : (0 : ℝ) < 1) hα1
    (fun x => groupConvolution_abs_le_source_mass G hu hsu hF hbound x)
  have hdifference : ∀ x y : ControlCarrier N,
      |G2.groupConvolution G u F x - G2.groupConvolution G u F y| ≤
        (M * mass) * (dist x y / 1 + (dist x y / 1) ^ 2) := by
    intro x y
    have hpoint (z : Fin N → ℝ) :
        |u z * F (G.mul (G.inv z) x) - u z * F (G.mul (G.inv z) y)| ≤
          |u z| * (M * (dist x y + dist x y ^ 2)) := by
      rw [← mul_sub, abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      have hh := hmod (G.mul (G.inv z) x) (G.mul (G.inv z) y)
      rw [G2.gaugeDistance_leftInvariant G ν x y (G.inv z)] at hh
      exact hh
    rw [G2.groupConvolution_eq_integral, G2.groupConvolution_eq_integral,
      ← integral_sub (hex x) (hex y)]
    calc
      _ ≤ ∫ z, |u z * F (G.mul (G.inv z) x) - u z * F (G.mul (G.inv z) y)| := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
          (fun z => u z * F (G.mul (G.inv z) x) - u z * F (G.mul (G.inv z) y))
      _ ≤ ∫ z, |u z| * (M * (dist x y + dist x y ^ 2)) :=
        integral_mono ((hex x).sub (hex y)).norm (huabs.mul_const _) hpoint
      _ = _ := by rw [integral_mul_const]; dsimp [mass]; ring
  have hh := hn hdifference
  have he : M * mass + 2 * (M * mass) / (1 : ℝ) ^ (α : ℝ) = 3 * M * mass := by
    rw [Real.one_rpow, div_one]
    ring
  rw [he] at hh
  exact hh

/-- far part. Actual invariant field derivative bounds
produce the kernel modulus through the full control-curve theorem. -/
theorem groupConvolution_holderNorm_of_field_bounds {q : ℕ}
    {Y : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)}
    (H : G2.ControlNormConclusion G driftWeight Y)
    {u F : (Fin N → ℝ) → ℝ} (hu : Continuous u) (hsu : HasCompactSupport u)
    (hF : ContDiff ℝ 1 F) {M D : ℝ} {C : Fin q → ℝ}
    (hM : 0 ≤ M) (hbound : ∀ x, |F x| ≤ M)
    (hfirst : ∀ x, ∀ i : Fin q, |fderiv ℝ F x (Y i.succ x)| ≤ C i)
    (hdrift : ∀ x, |fderiv ℝ F x (Y 0 x)| ≤ D)
    (hC : (∑ i, C i) ≤ M) (hD : D ≤ M)
    {α : ℝ≥0} (hα1 : (α : ℝ) ≤ 1) :
    let metric : MetricSpace (ControlCarrier N) := gaugeMetric G H.norm H.constant_one H.symmetric
    @H2.boundedHolderNorm (ControlCarrier N) metric α univ
      (fun x => G2.groupConvolution G u F x) ≤ ENNReal.ofReal (3 * M * ∫ y, |u y|) := by
  apply groupConvolution_holderNorm_of_kernel_modulus G H.norm H.constant_one H.symmetric
    hu hsu hF.continuous hM hbound _ hα1
  intro x y
  have hh := global_meanValue_of_controlNorm H hF hfirst hdrift y x
  rw [← gaugeMetric_controlDistance G H y x] at hh
  change |F x - F y| ≤ G2.gaugeDistance G H.norm y x * (∑ i, C i) +
    G2.gaugeDistance G H.norm y x ^ 2 * D at hh
  rw [G2.gaugeDistance_symmetric G H.norm H.symmetric x y] at hh
  exact hh.trans (by
    calc
      _ ≤ G2.gaugeDistance G H.norm x y * M + G2.gaugeDistance G H.norm x y ^ 2 * M :=
        add_le_add (mul_le_mul_of_nonneg_left hC (show 0 ≤ G2.gaugeDistance G H.norm x y from
          @dist_nonneg (ControlCarrier N) (gaugeMetric G H.norm H.constant_one H.symmetric).toPseudoMetricSpace x y))
          (mul_le_mul_of_nonneg_left hD (sq_nonneg _))
      _ = _ := by ring)

end RothschildStein.H3
