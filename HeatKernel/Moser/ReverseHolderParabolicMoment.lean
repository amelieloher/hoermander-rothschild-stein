-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.ReverseHolderLocalizedEnergy
public import HeatKernel.Moser.MeanValueSobolevEnergyMoments
import all Mathlib.Basic.Real.Basic
import all Mathlib.Analysis.Normed.Group.Real
import all Mathlib.Analysis.Normed.Field.Basic

/-! Parabolic higher moments from backward small-positive-power energy budgets. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal
namespace HeatKernel

/-- One geometric Sobolev constant converts the backward budgets to a parabolic
higher moment. The cutoff error, graph-coordinate comparisons, and common time
representative budgets are explicit inputs. Its energy coefficient has no loss
in the small positive exponent. -/
theorem exists_uniform_reverse_holder_parabolic_moment_constant {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {ν : ℝ} (hν : max 2 (G.homogeneousDimension : ℝ) < ν) :
    ∃ A : ℝ, 1 ≤ A ∧
    let X := G.horizontalFields hq
    ∀ {V : Opens (Fin N → ℝ)},
      volume (V : Set (Fin N → ℝ)) ≠ ⊤ → ∀
    {a b ell H Lerror Lgradient : ℝ}
    (Y : ℝ → zeroBoundaryGraph V X) (θ e D R m : ℝ → ℝ),
    HasBackwardCutoffEnergyBudgets a b ell H Lerror Lgradient Y θ e D R m →
    let C := H + 2 * Lerror
    let w := fun t => θ t • Y t
    (∫⁻ t in Icc a b, ∫⁻ x,
      ‖(w t : GradientSpace (N := N) ⊤ q).fst x‖ₑ ^ (2 + 4 / ν) ∂volume) ≤
        ENNReal.ofReal A *
          (ENNReal.ofReal (C + C / ell + 2 * Lgradient + 1) *
            ENNReal.ofReal (∫ t in Icc a b, m t)) ^ (1 + 2 / ν) := by
  obtain ⟨A, hA, hSob⟩ :=
    exists_uniform_parabolic_moment_constant_of_energy_bounds G hq hqpos hspan hw hν
  refine ⟨A, hA, ?_⟩
  dsimp only
  intro V hfinite a b ell H Lerror Lgradient Y θ e D R m h
  obtain ⟨hwm, hslice, henergy⟩ :=
    reverse_holder_localized_graph_energy_bounds_of_initial_budgets h
  exact hSob V hfinite (volume.restrict (Icc a b)) (fun t => θ t • Y t) hwm
    ((H + 2 * Lerror) + (H + 2 * Lerror) / ell + 2 * Lgradient + 1)
    (∫ t in Icc a b, m t)
    (by have := h.time_cost_nonneg; have := h.error_cost_nonneg
        have := h.gradient_cost_nonneg; have := h.ellipticity_pos; positivity)
    (integral_nonneg_of_ae h.moment_nonneg) hslice henergy

end HeatKernel
