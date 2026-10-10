-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Geometry.HorizontalCurve
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Topology.Algebra.MetricSpace.Lipschitz

/-! The continuously differentiable chain rule along horizontal curves. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace HeatKernel

/-- A function continuously differentiable near a compact curve image is Lipschitz
on that image. -/
theorem exists_lipschitzOnWith_curve_image {N : ℕ} {γ : ℝ → (Fin N → ℝ)}
    {s t : ℝ} {f : (Fin N → ℝ) → ℝ}
    (hγ : AbsolutelyContinuousOnInterval γ s t)
    (hf : ∀ x ∈ γ '' uIcc s t, ContDiffAt ℝ 1 f x) :
    ∃ K, LipschitzOnWith K f (γ '' uIcc s t) := by
  apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_uIcc.image_of_continuousOn hγ.continuousOn)
  intro x hx
  obtain ⟨K, V, hV, hK⟩ := (hf x hx).exists_lipschitzOnWith
  exact ⟨K, V, mem_nhdsWithin_of_mem_nhds hV, hK⟩

/-- The composition of a horizontal curve with a function continuously differentiable
near its image is absolutely continuous. -/
theorem IsHorizontalCurveOn.absolutelyContinuous_comp {N q : ℕ}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)} {γ : ℝ → (Fin N → ℝ)}
    {a : Fin q → ℝ → ℝ} {s t : ℝ} (h : IsHorizontalCurveOn X γ a s t)
    {f : (Fin N → ℝ) → ℝ} (hf : ∀ x ∈ γ '' uIcc s t, ContDiffAt ℝ 1 f x) :
    AbsolutelyContinuousOnInterval (f ∘ γ) s t := by
  obtain ⟨K, hK⟩ := exists_lipschitzOnWith_curve_image h.absolutelyContinuous hf
  exact hK.comp_absolutelyContinuousOnInterval (fun u hu => mem_image_of_mem γ hu)
    h.absolutelyContinuous

/-- The derivative of a smooth function along a horizontal curve is the control-weighted
sum of its horizontal directional derivatives almost everywhere. -/
theorem IsHorizontalCurveOn.hasDerivAt_comp {N q : ℕ}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)} {γ : ℝ → (Fin N → ℝ)}
    {a : Fin q → ℝ → ℝ} {s t : ℝ} (h : IsHorizontalCurveOn X γ a s t)
    {f : (Fin N → ℝ) → ℝ} (hf : ∀ x ∈ γ '' uIcc s t, ContDiffAt ℝ 1 f x) :
    ∀ᵐ u ∂volume.restrict (Icc s t),
      HasDerivAt (f ∘ γ) (∑ i, a i u * fderiv ℝ f (γ u) (X i (γ u))) u := by
  filter_upwards [h.hasDerivAt, ae_restrict_mem measurableSet_Icc] with u hu humem
  have hfu := (hf (γ u) (mem_image_of_mem γ (Icc_subset_uIcc humem))).differentiableAt
    (by norm_num)
  have hd := hfu.hasFDerivAt.comp_hasDerivAt u hu
  simpa only [map_sum, map_smul, smul_eq_mul] using hd

end HeatKernel
