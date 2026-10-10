-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Bridge.SpatialValueFunctional
public import HeatKernel.Bridge.ZeroBoundaryDualRestriction
public import HeatKernel.Bridge.SpatialZeroExtension
public import HeatKernel.Form.BochnerFlux
public import HeatKernel.Sobolev.ZeroBoundarySupport
import Mathlib.Tactic
import all Mathlib.Basic.Real.Basic

/-! # Local square-integrable values in the zero-boundary form dual -/

@[expose] public section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal
namespace HeatKernel

/-- Local joint square integrability gives a dual-valued L² curve whose
 evaluation is the literal value pairing on every contained zero-boundary domain. -/
theorem exists_localized_dual_value_curve {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [SFinite μ] {N q : ℕ}
    (V : Opens (Fin N → ℝ)) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    {K : Set (Fin N → ℝ)} (hK : MeasurableSet K) (hVK : (V : Set (Fin N → ℝ)) ⊆ K)
    (f : α × (Fin N → ℝ) → ℝ) (hf : MemLp f 2 (μ.prod (volume.restrict K))) :
    ∃ D : α → (zeroBoundaryGraph V X →L[ℝ] ℝ), MemLp D 2 μ ∧
      ∀ᵐ t ∂μ, ∀ v : zeroBoundaryGraph V X,
        D t v = ∫ x, f (t, x) * (v : GradientSpace (N := N) ⊤ q).fst x := by
  let : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  let : IsSeparable (volume.restrict ((⊤ : Opens (Fin N → ℝ)) : Set (Fin N → ℝ))) :=
    isSeparable_of_sigmaFinite _
  let h : α → (Fin N → ℝ) → ℝ := fun t => K.indicator (fun x => f (t, x))
  have hh : MemLp (Function.uncurry h) 2
      (μ.prod (volume.restrict ((⊤ : Opens (Fin N → ℝ)) : Set (Fin N → ℝ)))) := by
    change MemLp (fun z : α × (Fin N → ℝ) =>
      K.indicator (fun x => f (z.1, x)) z.2) 2
      (μ.prod (volume.restrict ((⊤ : Opens (Fin N → ℝ)) : Set (Fin N → ℝ))))
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      memLp_two_spatial_zero_extension hK hf
  obtain ⟨H, hH, hr⟩ := exists_L2_curve_of_product_memLp hh
  refine ⟨fun t => zeroBoundaryDualRestriction V X (spatialValueFunctional ⊤ X (H t)),
    memLp_zeroBoundaryDualRestriction V X (memLp_spatialValueFunctional ⊤ X hH), ?_⟩
  filter_upwards [hr] with t ht
  intro v
  rw [zeroBoundaryDualRestriction_apply, spatialValueFunctional_apply]
  simp only [Opens.coe_top, Measure.restrict_univ]
  apply integral_congr_ae
  have ht' : (H t : (Fin N → ℝ) → ℝ) =ᵐ[volume] h t := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using ht
  filter_upwards [ht', Sobolev.ae_eq_zero_outside_of_mem_zeroBoundaryGraph V X v] with x hx hv
  change H t x * (v : GradientSpace (N := N) ⊤ q).fst x = _
  rw [hx]
  change K.indicator (fun y => f (t, y)) x *
    (v : GradientSpace (N := N) ⊤ q).fst x = _
  by_cases hxK : x ∈ K
  · rw [Set.indicator_of_mem hxK]
  · rw [Set.indicator_of_notMem hxK, hv (fun hxV => hxK (hVK hxV))]
    simp

end HeatKernel
