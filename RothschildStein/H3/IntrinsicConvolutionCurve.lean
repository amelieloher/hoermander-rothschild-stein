-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.IntrinsicTranslation
public import RothschildStein.H3.IntrinsicCurveDerivative
public import RothschildStein.G2.ConvolutionSubstitution
public import Mathlib.Analysis.Calculus.ParametricIntegral

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology
attribute [local irreducible] RothschildStein.HomogeneousGroup.inv RothschildStein.HomogeneousGroup.mul
namespace RothschildStein.H3
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Differentiation under group convolution along an actual
integral curve. Continuous bounded intrinsic data suffice; no Euclidean
scalar differentiability is imposed (BB Prop 2.22 and p. 122). -/
theorem hasDerivAt_convolution_curve_of_intrinsic
    (X : (Fin N → ℝ) → (Fin N → ℝ)) (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (hleft : G2.IsLeftInvariantField G X)
    {ψ f g : (Fin N → ℝ) → ℝ} (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ)
    (hf : Continuous f) (hg : Continuous g) (hfg : hasIntrinsicDeriv ⊤ X f g)
    {Mf Mg : ℝ} (hMf : ∀ z, |f z| ≤ Mf) (hMg : ∀ z, |g z| ≤ Mg)
    {J : Set ℝ} (hJ : IsOpen J) {γ : ℝ → (Fin N → ℝ)}
    (hγ : IsIntegralCurveOn γ (fun _ => X) J) {t : ℝ} (ht : t ∈ J) :
    HasDerivAt (fun s => G2.groupConvolution G ψ f (γ s))
      (G2.groupConvolution G ψ g (γ t)) t := by
  have hiψ : Integrable ψ := hψ.integrable_of_hasCompactSupport hcψ
  have hm (h : (Fin N → ℝ) → ℝ) (hh : Continuous h) (s : ℝ) :
      AEStronglyMeasurable (fun y => ψ y * h (G.mul (G.inv y) (γ s))) volume :=
    (hψ.mul (hh.comp ((G2.continuous_mul G).comp
      ((G2.continuous_inv G).prodMk continuous_const)))).aestronglyMeasurable
  have hi : Integrable (fun y => ψ y * f (G.mul (G.inv y) (γ t))) volume := by
    apply Integrable.mono' (hiψ.norm.mul_const Mf) (hm f hf t)
    exact Eventually.of_forall fun y => by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hMf _) (abs_nonneg _)
  have hd (y : Fin N → ℝ) (s : ℝ) (hs : s ∈ J) :
      HasDerivAt (fun r => ψ y * f (G.mul (G.inv y) (γ r)))
        (ψ y * g (G.mul (G.inv y) (γ s))) s := by
    have htr := hasIntrinsicDeriv_leftTranslation G ⊤ X hX hleft (G.inv y) hfg
    change hasIntrinsicDeriv ⊤ X (f ∘ G.mul (G.inv y)) (g ∘ G.mul (G.inv y)) at htr
    have hc := hasDerivAt_comp_curve_of_intrinsic ⊤ X htr
      (hγ.isIntegralCurveAt (hJ.mem_nhds hs)) (Eventually.of_forall fun _ => mem_univ _)
    simpa only [Function.comp_def] using hc.const_mul (ψ y)
  have he := hasDerivAt_integral_of_dominated_loc_of_deriv_le (hJ.mem_nhds ht)
    (Eventually.of_forall fun s => hm f hf s) hi (hm g hg t)
    (bound := fun y => |ψ y| * Mg)
    (Eventually.of_forall fun y => fun s _ => by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hMg _) (abs_nonneg _))
    (hiψ.norm.mul_const Mg) (Eventually.of_forall hd)
  simpa only [G2.groupConvolution_eq_integral] using he.2

end RothschildStein.H3
