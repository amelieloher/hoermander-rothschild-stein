-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.ReverseHolderInitialMomentBudget
public import HeatKernel.Moser.NegativePowerLocalizedEnergy
import all Mathlib.Basic.Real.Basic
import all Mathlib.Analysis.Normed.Group.Real
import all Mathlib.Analysis.Normed.Field.Basic

/-! Localized graph energy from backward small-power budgets. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace HeatKernel

/-- Quantitative backward energy data for a spatially localized graph curve.
The common time representative and the geometric moment comparisons are recorded
separately from the differential equation that supplies them. -/
structure HasBackwardCutoffEnergyBudgets {N q : ℕ}
    {V : Opens (Fin N → ℝ)} {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (a b ell H Lerror Lgradient : ℝ) (Y : ℝ → zeroBoundaryGraph V X)
    (θ e D R m : ℝ → ℝ) : Prop where
  interval_lt : a < b
  ellipticity_pos : 0 < ell
  time_cost_nonneg : 0 ≤ H
  error_cost_nonneg : 0 ≤ Lerror
  gradient_cost_nonneg : 0 ≤ Lgradient
  curve_memLp : MemLp Y 2 (volume.restrict (Icc a b))
  cutoff_contDiff : ContDiff ℝ 1 θ
  cutoff_unit : ∀ t ∈ Icc a b, θ t ∈ Icc (0 : ℝ) 1
  neg_deriv_sq_le : ∀ t ∈ Icc a b, -(deriv (fun s => θ s ^ 2) t) ≤ H
  diffusion_integrable : IntegrableOn D (Icc a b)
  error_integrable : IntegrableOn R (Icc a b)
  moment_integrable : IntegrableOn m (Icc a b)
  diffusion_nonneg : ∀ᵐ t ∂volume.restrict (Icc a b), 0 ≤ D t
  moment_nonneg : ∀ᵐ t ∂volume.restrict (Icc a b), 0 ≤ m t
  error_le : ∀ᵐ t ∂volume.restrict (Icc a b), R t ≤ 2 * Lerror * m t
  value_le : ∀ᵐ t ∂volume.restrict (Icc a b),
    ‖(Y t : GradientSpace (N := N) ⊤ q).fst‖ ^ 2 ≤ m t
  gradient_le : ∀ᵐ t ∂volume.restrict (Icc a b),
    ‖(Y t : GradientSpace (N := N) ⊤ q).snd‖ ^ 2 ≤ D t / ell + 2 * Lgradient * m t
  representative_ae_eq : e =ᵐ[volume.restrict (Icc a b)]
    (fun t => ‖(Y t : GradientSpace (N := N) ⊤ q).fst‖ ^ 2)
  initial_budget : ∀ s ∈ Icc a b,
    θ s ^ 2 * e s + (∫ t in s..b, θ t ^ 2 * D t) ≤
      (∫ t in s..b, -(deriv (fun s => θ s ^ 2) t) * e t) + ∫ t in s..b, θ t ^ 2 * R t

/-- Backward budgets for one common time representative give the slice and
integrated graph-energy bounds needed for parabolic Sobolev. The coefficient
is independent of the small power. -/
theorem reverse_holder_localized_graph_energy_bounds_of_initial_budgets {N q : ℕ}
    {V : Opens (Fin N → ℝ)} {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    {a b ell H Lerror Lgradient : ℝ} {Y : ℝ → zeroBoundaryGraph V X}
    {θ e D R m : ℝ → ℝ}
    (h : HasBackwardCutoffEnergyBudgets a b ell H Lerror Lgradient Y θ e D R m) :
    let C := H + 2 * Lerror
    let w := fun t => θ t • Y t
    MemLp w 2 (volume.restrict (Icc a b)) ∧
      (∀ᵐ t ∂volume.restrict (Icc a b),
        ‖(w t : GradientSpace (N := N) ⊤ q).fst‖ ^ 2 ≤
          (C + C / ell + 2 * Lgradient + 1) * (∫ s in Icc a b, m s)) ∧
      (∫ t in Icc a b, ‖(w t : GradientSpace (N := N) ⊤ q).snd‖ ^ 2 +
        ‖(w t : GradientSpace (N := N) ⊤ q).fst‖ ^ 2) ≤
          (C + C / ell + 2 * Lgradient + 1) * (∫ t in Icc a b, m t) := by
  rcases h with ⟨hab, hell, hH, hLerror, hLgradient, hY, hθ, hθunit, hθderiv,
    hD, hR, hm, hD0, hm0, hRbound, hvalue, hgradient, heq, hbudget⟩
  have hEi : IntegrableOn
      (fun t => ‖(Y t : GradientSpace (N := N) ⊤ q).fst‖ ^ 2) (Icc a b) := by
    change Integrable (fun t => ‖(Y t : GradientSpace (N := N) ⊤ q).fst‖ ^ 2)
      (volume.restrict (Icc a b))
    simpa only [zero_pow (by decide : 2 ≠ 0), zero_mul, zero_add] using
      integrable_zeroBoundary_scaled_energy V X (volume.restrict (Icc a b)) hY 0
  have hχunit (t : ℝ) (ht : t ∈ Icc a b) : θ t ^ 2 ∈ Icc (0 : ℝ) 1 :=
    ⟨sq_nonneg _, by nlinarith [(hθunit t ht).1, (hθunit t ht).2]⟩
  have hbudget' := ae_initial_energy_budgets_of_representative heq hEi hR (hθ.pow 2) hbudget
  obtain ⟨hslice, htotal⟩ := initial_energy_budget_le_full_value_moment hab hH hLerror
    hEi hD hR hm hRbound hm0 hD0 (Filter.Eventually.of_forall fun t => sq_nonneg _)
    hvalue (hθ.pow 2) hχunit hθderiv hbudget'
  exact reciprocal_localized_graph_energy_bounds hell (by positivity : 0 ≤ H + 2 * Lerror)
    hLgradient hY hθ.continuous hθunit hD hm hD0 hm0 hvalue hgradient hslice htotal

end HeatKernel
