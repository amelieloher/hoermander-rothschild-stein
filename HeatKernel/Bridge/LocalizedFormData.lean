-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Bridge.SpaceTimeMultipliers
public import HeatKernel.Bridge.SpatialZeroExtension
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Tactic.Linter

/-! # Square-integrable localized value and coefficient-flux data for form tests -/

@[expose] public section
open Set MeasureTheory
namespace HeatKernel

/-- Local L² data, bounded measurable coefficients, and compact continuous time
multipliers produce global spatial L² representatives for value and flux testing. -/
theorem exists_localized_square_integrable_form_data {β : Type*} [MeasurableSpace β]
    {μ : Measure ℝ} {ν : Measure β} [SFinite μ] [SFinite ν] {q : ℕ} {K : Set β} (hK : MeasurableSet K)
    (u : ℝ × β → ℝ) (g : Fin q → ℝ × β → ℝ)
    (a : Fin q → Fin q → ℝ × β → ℝ)
    (hu : MemLp u 2 (μ.prod (ν.restrict K)))
    (hg : ∀ j, MemLp (g j) 2 (μ.prod (ν.restrict K)))
    (ha : ∀ i j, AEStronglyMeasurable (a i j) (μ.prod (ν.restrict K)))
    {C : ℝ} (hbound : ∀ i j, ∀ᵐ z ∂(μ.prod (ν.restrict K)), ‖a i j z‖ ≤ C)
    {χ ψ : ℝ → ℝ} (hχ : Continuous χ) (hcχ : HasCompactSupport χ)
    (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) :
    ∃ (T : Lp ℝ 2 (μ.prod ν)) (F : Fin q → Lp ℝ 2 (μ.prod ν)),
      (T : ℝ × β → ℝ) =ᵐ[μ.prod ν]
        (fun z => K.indicator (fun x => χ z.1 * u (z.1, x)) z.2) ∧
      ∀ i, (F i : ℝ × β → ℝ) =ᵐ[μ.prod ν]
        (fun z => K.indicator (fun x => ψ z.1 * ∑ j, a i j (z.1, x) * g j (z.1, x)) z.2) := by
  have htlocal := memLp_two_mul_time_of_compact_support hu hχ hcχ
  have ht := memLp_two_spatial_zero_extension hK htlocal
  have hflux (i : Fin q) := memLp_two_matrix_flux ha hg hbound i
  have hflocal (i : Fin q) := memLp_two_mul_time_of_compact_support (hflux i) hψ hcψ
  have hf (i : Fin q) := memLp_two_spatial_zero_extension hK (hflocal i)
  refine ⟨ht.toLp _, fun i => (hf i).toLp _, ht.coeFn_toLp, fun i => ?_⟩
  exact (hf i).coeFn_toLp

end HeatKernel
