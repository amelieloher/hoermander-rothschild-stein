-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Bridge.DualFluxCurves
public import HeatKernel.Bridge.ZeroBoundaryDualRestriction
public import HeatKernel.Bridge.SpatialZeroExtension
public import HeatKernel.Sobolev.ZeroBoundaryGradientSupport
import Mathlib.Tactic
import all Mathlib.Basic.Real.Basic

/-! # Local horizontal fluxes in the zero-boundary form dual -/

@[expose] public section
open Set MeasureTheory TopologicalSpace
namespace HeatKernel

/-- Local joint L² flux data determine an L² curve in the zero-boundary form
 dual. Zero extension disappears from its literal integral evaluation. -/
theorem exists_localized_dual_flux_curve {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [SFinite μ] {N q : ℕ}
    (V : Opens (Fin N → ℝ)) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    {K : Set (Fin N → ℝ)} (hK : MeasurableSet K) (hVK : (V : Set (Fin N → ℝ)) ⊆ K)
    (f : Fin q → α × (Fin N → ℝ) → ℝ)
    (hf : ∀ i, MemLp (f i) 2 (μ.prod (volume.restrict K))) :
    ∃ F : α → (zeroBoundaryGraph V X →L[ℝ] ℝ), MemLp F 2 μ ∧
      ∀ᵐ t ∂μ, ∀ v : zeroBoundaryGraph V X,
        F t v = ∑ i, ∫ x, f i (t, x) * (v : GradientSpace (N := N) ⊤ q).snd i x := by
  let h : Fin q → α → (Fin N → ℝ) → ℝ :=
    fun i t => K.indicator (fun x => f i (t, x))
  have hh (i : Fin q) : MemLp (Function.uncurry (h i)) 2
      (μ.prod (volume.restrict ((⊤ : Opens (Fin N → ℝ)) : Set (Fin N → ℝ)))) := by
    change MemLp (fun z : α × (Fin N → ℝ) =>
      K.indicator (fun x => f i (z.1, x)) z.2) 2
      (μ.prod (volume.restrict ((⊤ : Opens (Fin N → ℝ)) : Set (Fin N → ℝ))))
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      memLp_two_spatial_zero_extension hK (hf i)
  obtain ⟨D, hD, hr⟩ := exists_dual_flux_curve_of_product_memLp ⊤ X h hh
  refine ⟨fun t => zeroBoundaryDualRestriction V X (D t),
    memLp_zeroBoundaryDualRestriction V X hD, ?_⟩
  filter_upwards [hr] with t ht
  intro v
  rw [zeroBoundaryDualRestriction_apply, ht]
  simp only [Opens.coe_top, Measure.restrict_univ]
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  filter_upwards [Sobolev.ae_eq_zero_gradient_outside_of_mem_zeroBoundaryGraph V X v i]
    with x hx
  change K.indicator (fun y => f i (t, y)) x *
    (v : GradientSpace (N := N) ⊤ q).snd i x = _
  by_cases hxK : x ∈ K
  · rw [Set.indicator_of_mem hxK]
  · rw [Set.indicator_of_notMem hxK, hx (fun hxV => hxK (hVK hxV))]
    simp

/-- Bounded measurable coefficients applied to local L² gradient components
produce an L² curve in the dual of any contained zero-boundary form domain. -/
theorem exists_localized_dual_matrix_flux_curve {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [SFinite μ] {N q : ℕ}
    (V : Opens (Fin N → ℝ)) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    {K : Set (Fin N → ℝ)} (hK : MeasurableSet K) (hVK : (V : Set (Fin N → ℝ)) ⊆ K)
    (a : Fin q → Fin q → α × (Fin N → ℝ) → ℝ)
    (g : Fin q → α × (Fin N → ℝ) → ℝ) {C : ℝ}
    (ha : ∀ i j, AEStronglyMeasurable (a i j) (μ.prod (volume.restrict K)))
    (hg : ∀ j, MemLp (g j) 2 (μ.prod (volume.restrict K)))
    (hb : ∀ i j, ∀ᵐ z ∂μ.prod (volume.restrict K), ‖a i j z‖ ≤ C) :
    ∃ F : α → (zeroBoundaryGraph V X →L[ℝ] ℝ), MemLp F 2 μ ∧
      ∀ᵐ t ∂μ, ∀ v : zeroBoundaryGraph V X,
        F t v = ∑ i, ∫ x, (∑ j, a i j (t, x) * g j (t, x)) *
          (v : GradientSpace (N := N) ⊤ q).snd i x :=
  exists_localized_dual_flux_curve V X hK hVK
    (fun i z => ∑ j, a i j z * g j z) (fun i => memLp_two_matrix_flux ha hg hb i)

end HeatKernel
