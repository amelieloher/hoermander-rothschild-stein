-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Bridge.SpatialValueFunctional
public import HeatKernel.Bridge.DualEnergyPair
import Mathlib.Tactic
import all Mathlib.Basic.Real.Basic

/-! # Identifying cutoff energy values in the form dual -/

@[expose] public section
open Set MeasureTheory TopologicalSpace
namespace HeatKernel

/-- A dual curve with the cutoff value evaluations is almost everywhere the
spatial L² functional of every energy curve representing that cutoff value. -/
theorem ae_eq_spatialValueFunctional_of_cutoff_representatives
    {T : Type*} [MeasurableSpace T] {μ : Measure T} {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (v : T → energyGraph (N := N) ⊤ X)
    {u : T → (Fin N → ℝ) → ℝ} {φ : (Fin N → ℝ) → ℝ}
    {D : T → (energyGraph (N := N) ⊤ X →L[ℝ] ℝ)}
    (hv : ∀ᵐ t ∂μ, (v t : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
      fun x => u t x * φ x)
    (hD : ∀ᵐ t ∂μ, ∀ w : energyGraph (N := N) ⊤ X,
      D t w = ∫ x, u t x * (φ x * (w : GradientSpace (N := N) ⊤ q).fst x)) :
    D =ᵐ[μ] fun t => spatialValueFunctional ⊤ X (v t : GradientSpace (N := N) ⊤ q).fst := by
  filter_upwards [hv, hD] with t ht hd
  ext w
  rw [hd w, spatialValueFunctional_apply]
  simp only [Opens.coe_top, Measure.restrict_univ]
  apply integral_congr_ae
  filter_upwards [ht] with x hx
  rw [hx]
  ring

/-- The time equation of a cutoff dual pair holds for the actual spatial L²
functional of any energy curve representing its cutoff value. -/
theorem IsDualEnergyPair.cutoff_value_time_balance {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)) {J : Set ℝ}
    {u : ℝ → (Fin N → ℝ) → ℝ} {φ : (Fin N → ℝ) → ℝ}
    {flux : ℝ → energyGraph (N := N) ⊤ X → ℝ}
    {D F : ℝ → (energyGraph (N := N) ⊤ X →L[ℝ] ℝ)}
    (h : IsDualEnergyPair (E := energyGraph (N := N) ⊤ X) J
      (fun t w => ∫ x, u t x * (φ x * (w : GradientSpace (N := N) ⊤ q).fst x)) flux D F)
    (v : ℝ → energyGraph (N := N) ⊤ X)
    (hv : ∀ᵐ t ∂volume.restrict J, (v t : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
      fun x => u t x * φ x) :
    SatisfiesDualTimeBalance J
      (fun t => spatialValueFunctional ⊤ X (v t : GradientSpace (N := N) ⊤ q).fst) F := by
  exact h.2.2.2.2.congr
    (ae_eq_spatialValueFunctional_of_cutoff_representatives X v hv h.2.2.1)
    Filter.EventuallyEq.rfl

end HeatKernel
