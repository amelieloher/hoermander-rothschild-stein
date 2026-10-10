-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Geometry.AffineReparametrization
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Topology.Algebra.MetricSpace.Lipschitz

/-! Smooth changes of spatial coordinates for horizontal competitors. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped BigOperators NNReal
namespace HeatKernel

/-- A smooth map carrying each horizontal field to a common positive multiple of a target
field carries horizontal curves to curves with correspondingly scaled controls. -/
theorem IsHorizontalCurveOn.map {N M q : ℕ}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    {Y : Fin q → (Fin M → ℝ) → (Fin M → ℝ)}
    {γ : ℝ → (Fin N → ℝ)} {a : Fin q → ℝ → ℝ} {s t c : ℝ}
    (h : IsHorizontalCurveOn X γ a s t) {f : (Fin N → ℝ) → (Fin M → ℝ)}
    (hf : ContDiff ℝ 1 f) (hc : 0 < c)
    (hmap : ∀ i x, fderiv ℝ f x (X i x) = c • Y i (f x)) :
    IsHorizontalCurveOn Y (f ∘ γ) (fun i u => c * a i u) s t := by
  have hloc : LocallyLipschitzOn (γ '' uIcc s t) f := by
    intro x _
    obtain ⟨K, V, hV, hK⟩ := hf.contDiffAt.exists_lipschitzOnWith
    exact ⟨K, V, mem_nhdsWithin_of_mem_nhds hV, hK⟩
  obtain ⟨K, hK⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_uIcc.image_of_continuousOn h.absolutelyContinuous.continuousOn) hloc
  refine ⟨hK.comp_absolutelyContinuousOnInterval (fun u hu => mem_image_of_mem γ hu)
    h.absolutelyContinuous, fun i => aemeasurable_const.mul (h.aemeasurable i), ?_, ?_⟩
  · have he : controlNorm (fun i u => c * a i u) = fun u => c * controlNorm a u := by
      funext u
      rw [controlNorm_mul, abs_of_pos hc]
    rw [he]
    exact h.integrable_norm.const_mul c
  · filter_upwards [h.hasDerivAt] with u hu
    have hd := (hf.differentiable (by norm_num)).differentiableAt.hasFDerivAt.comp_hasDerivAt u hu
    simpa only [Function.comp_apply, map_sum, map_smul, hmap, smul_smul, mul_comm] using hd

/-- A positive covariance factor bounds the target horizontal distance by the scaled
source distance. -/
theorem horizontalL2Distance_map_le {N M q : ℕ}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    {Y : Fin q → (Fin M → ℝ) → (Fin M → ℝ)}
    {f : (Fin N → ℝ) → (Fin M → ℝ)} {c : ℝ}
    (hf : ContDiff ℝ 1 f) (hc : 0 < c)
    (hmap : ∀ i x, fderiv ℝ f x (X i x) = c • Y i (f x)) (x y : Fin N → ℝ) :
    horizontalL2Distance Y (f x) (f y) ≤ ENNReal.ofReal c * horizontalL2Distance X x y := by
  unfold horizontalL2Distance
  simp_rw [sInf_eq_iInf, ENNReal.mul_iInf_of_ne
    (ne_of_gt (ENNReal.ofReal_pos.mpr hc)) ENNReal.ofReal_ne_top]
  apply le_iInf₂
  intro r
  rintro ⟨γ, a, hac, hzero, hone, hmeas, hint, hderiv, rfl⟩
  have h : IsHorizontalCurveOn X γ a 0 1 := ⟨hac, hmeas, hint, hderiv⟩
  have hb := horizontalL2Distance_le_controlLength (h.map hf hc hmap)
  simp_rw [controlNorm_mul, abs_of_pos hc] at hb
  rw [integral_const_mul, ENNReal.ofReal_mul hc.le] at hb
  simpa only [Function.comp_apply, hzero, hone, horizontalL2Distance, controlNorm, sInf_eq_iInf] using hb

end HeatKernel
