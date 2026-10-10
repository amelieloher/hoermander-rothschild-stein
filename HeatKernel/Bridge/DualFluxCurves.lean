-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Bridge.HorizontalFluxFunctional
public import HeatKernel.Form.BochnerFlux
import Mathlib.Tactic
import all Mathlib.Basic.Real.Basic

/-! # Dual-valued L² curves representing measurable horizontal fluxes -/

@[expose] public section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal
namespace HeatKernel

/-- Jointly square-integrable flux components give a dual-valued L² curve
with one common almost-everywhere set for all form tests. -/
theorem exists_dual_flux_curve_of_product_memLp {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [SFinite μ] {N q : ℕ}
    (U : Opens (Fin N → ℝ)) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (f : Fin q → α → (Fin N → ℝ) → ℝ)
    (hf : ∀ i, MemLp (Function.uncurry (f i)) 2
      (μ.prod (volume.restrict (U : Set (Fin N → ℝ))))) :
    ∃ F : α → (energyGraph U X →L[ℝ] ℝ), MemLp F 2 μ ∧
      ∀ᵐ t ∂μ, ∀ v : energyGraph U X,
        F t v = ∑ i, ∫ x, f i t x * (v : GradientSpace U q).snd i x
          ∂volume.restrict (U : Set (Fin N → ℝ)) := by
  let : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  let : IsSeparable (volume.restrict (U : Set (Fin N → ℝ))) := isSeparable_of_sigmaFinite _
  choose J hJ hr using fun i => exists_L2_curve_of_product_memLp (hf i)
  let H : α → PiLp 2 (fun _ : Fin q => SpatialL2 U) :=
    fun t => WithLp.toLp 2 (fun i => J i t)
  have hH : MemLp H 2 μ := by
    rw [← memLp_comp_continuousLinearEquiv_iff
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin q => SpatialL2 U)) H, memLp_pi_iff]
    exact hJ
  refine ⟨fun t => horizontalFluxFunctional U X (H t),
    memLp_horizontalFluxFunctional U X hH, ?_⟩
  filter_upwards [ae_all_iff.mpr hr] with t ht
  intro v
  rw [horizontalFluxFunctional_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  filter_upwards [ht i] with x hx
  change J i t x * _ = _
  rw [hx]

end HeatKernel
