-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Geometry.LipschitzLocalForm
public import HeatKernel.Geometry.GroupCovariance
public import RothschildStein.G2.ConvolutionSmooth

/-! Nonnegative group smoothing preserves horizontal Lipschitz constants. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory RothschildStein
open scoped NNReal ENNReal BigOperators
namespace HeatKernel

/-- Left multiplication is an isometry of the horizontal metric carrier. -/
theorem CarnotPoint.dist_leftTranslation {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q ≤ N) (hqpos : 0 < q) (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (z : Fin N → ℝ) (x y : CarnotPoint G hq hqpos hspan) :
    @dist (CarnotPoint G hq hqpos hspan)
      (homogeneousHorizontalMetricSpace G hq hqpos hspan).toDist (G.mul z x) (G.mul z y) = dist x y := by
  unfold CarnotPoint at *
  change (horizontalL2Distance (G.horizontalFields hq) (G.mul z x) (G.mul z y)).toReal =
    (horizontalL2Distance (G.horizontalFields hq) x y).toReal
  rw [horizontalL2Distance_leftTranslation]

/-- A continuous compact kernel times a continuous translated input is integrable. -/
theorem integrable_group_smoothing {N : ℕ} (G : HomogeneousGroup N)
    {ρ f : (Fin N → ℝ) → ℝ} (hρ : Continuous ρ) (hc : HasCompactSupport ρ)
    (hf : Continuous f) (x : Fin N → ℝ) :
    Integrable (fun z => ρ z * f (G.mul (G.inv z) x)) volume := by
  have ht : Continuous (fun z => G.mul (G.inv z) x) := by
    apply continuous_pi
    intro j
    exact (MvPolynomial.continuous_eval (p := G.productPolynomial j)).comp
      (continuous_pi fun i => Sum.casesOn i
        (fun k => (continuous_apply k).comp (G2.continuous_inv G))
        (fun _ => continuous_const))
  exact (hρ.mul (hf.comp ht)).integrable_of_hasCompactSupport hc.mul_right

/-- A mass-one nonnegative kernel preserves a uniform bound on translated differences. -/
theorem abs_groupConvolution_sub_le {N : ℕ} (G : HomogeneousGroup N)
    {ρ f : (Fin N → ℝ) → ℝ} (hρ : Continuous ρ) (hc : HasCompactSupport ρ)
    (hf : Continuous f) (hn : ∀ z, 0 ≤ ρ z) (hm : ∫ z, ρ z = 1)
    (x y : Fin N → ℝ) {D : ℝ}
    (hb : ∀ z, |f (G.mul (G.inv z) x) - f (G.mul (G.inv z) y)| ≤ D) :
    |G2.groupConvolution G ρ f x - G2.groupConvolution G ρ f y| ≤ D := by
  have hi := integrable_group_smoothing G hρ hc hf
  rw [G2.groupConvolution_eq_integral, G2.groupConvolution_eq_integral,
    ← integral_sub (hi x) (hi y)]
  have hbound : ∀ z, |ρ z * f (G.mul (G.inv z) x) - ρ z * f (G.mul (G.inv z) y)| ≤ ρ z * D := by
    intro z
    rw [← mul_sub, abs_mul, abs_of_nonneg (hn z)]
    exact mul_le_mul_of_nonneg_left (hb z) (hn z)
  calc
    _ ≤ ∫ z, |ρ z * f (G.mul (G.inv z) x) - ρ z * f (G.mul (G.inv z) y)| := by
      simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm
          (fun z => ρ z * f (G.mul (G.inv z) x) - ρ z * f (G.mul (G.inv z) y)))
    _ ≤ ∫ z, ρ z * D :=
      integral_mono ((hi x).sub (hi y)).norm
        ((hρ.integrable_of_hasCompactSupport hc).mul_const D) hbound
    _ = D := by rw [integral_mul_const, hm, one_mul]

/-- Averaging left translates against a nonnegative mass-one kernel preserves the
horizontal Lipschitz constant. -/
theorem CarnotPoint.lipschitzWith_groupConvolution {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q ≤ N) (hqpos : 0 < q) (hspan : bracketSpansOn univ (G.horizontalFields hq))
    {ρ : (Fin N → ℝ) → ℝ} (hρ : Continuous ρ) (hc : HasCompactSupport ρ)
    (hn : ∀ z, 0 ≤ ρ z) (hm : ∫ z, ρ z = 1)
    {L : ℝ≥0} {f : CarnotPoint G hq hqpos hspan → ℝ} (hf : LipschitzWith L f) :
    LipschitzWith (α := CarnotPoint G hq hqpos hspan) L (G2.groupConvolution G ρ f) := by
  have hfc : Continuous (show (Fin N → ℝ) → ℝ from f) := hf.continuous
  apply LipschitzWith.of_dist_le_mul (α := CarnotPoint G hq hqpos hspan)
  intro x y
  apply abs_groupConvolution_sub_le G hρ hc hfc hn hm x y
  intro z
  let xz : CarnotPoint G hq hqpos hspan := G.mul (G.inv z) x
  let yz : CarnotPoint G hq hqpos hspan := G.mul (G.inv z) y
  have he : dist xz yz = dist x y := dist_leftTranslation G hq hqpos hspan (G.inv z) x y
  have hh : |f xz - f yz| ≤ (L : ℝ) * dist x y := by
    simpa only [Real.dist_eq] using
      (hf.dist_le_mul xz yz).trans_eq (congrArg (fun d : ℝ => (L : ℝ) * d) he)
  exact hh

end HeatKernel
