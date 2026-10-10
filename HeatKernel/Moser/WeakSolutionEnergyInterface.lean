-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Bridge.ZeroBoundaryWeakCutoffTimeWitness
public import HeatKernel.Moser.WeakSolutionEnergyTesting
public import HeatKernel.Moser.WeakSolutionNonlinearIdentity
public import HeatKernel.Moser.NonlinearAveragePairingLimits

/-! # A common energy interface for local weak solutions

One specified gradient carries both smooth spacetime and stationary energy testing,
local energy bounds, and zero-boundary weak-cutoff dual time equations. The flux in
`IsZeroBoundaryWeakCutoffEnergyTimePair` is positive spatial divergence-form energy:
its time equation reads integral χ' value = integral χ flux, hence ∂ₜ value = −flux.
Nonlinear tests use `WeakSolutionScalarTest` and its normalized primitive. This interface
concerns solutions; estimates for subsolutions require their own inequality hypothesis.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set MeasureTheory TopologicalSpace RothschildStein

namespace HeatKernel

/-- Compatible energy and test data for one specified weak gradient. -/
structure WeakSolutionEnergyInterface {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (a : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ)
    (I : Opens ℝ) (U : Opens (Fin N → ℝ))
    (u : ℝ → (Fin N → ℝ) → ℝ) (g : Fin q → ℝ → (Fin N → ℝ) → ℝ) : Prop where
  /-- The same weak gradient is used throughout. -/
  weak_gradient : ∀ᵐ t ∂volume.restrict (I : Set ℝ), ∀ i,
    hasWeakWordDeriv X U [i] (u t) (g i t)
  /-- Local L² gradient bounds and essential L∞ time bounds on values. -/
  local_bounds : HasLocalParabolicEnergyBounds I U u g
  /-- Smooth spacetime testing. -/
  spacetime_tests : SatisfiesParabolicTestIdentity X a I U u g
  /-- All stationary energy tests. -/
  stationary_tests : HasStationaryEnergyTestIdentity X a I U u g
  /-- Compact weak spatial cutoffs with their full dual time balance. -/
  cutoff_time_curves : HasZeroBoundaryWeakCutoffEnergyTimeCurves X a I U u g

/-- The literal weak-solution predicate supplies the common energy interface, with no
additional choice of gradient needed by downstream estimates. -/
theorem IsLocalWeakSolution.exists_weak_solution_energy_interface {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (a : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ)
    (I : Opens ℝ) (U : Opens (Fin N → ℝ)) {u : ℝ → (Fin N → ℝ) → ℝ}
    (hu : IsLocalWeakSolution G hq hqpos hw hspan a I U u)
    (ha : ∀ i j, Measurable (fun z : ℝ × (Fin N → ℝ) => a z.1 z.2 i j))
    {lower upper : ℝ} (hlower : 0 ≤ lower)
    (hbound : ∀ᵐ z : ℝ × (Fin N → ℝ) ∂volume,
      (∀ i j, a z.1 z.2 i j = a z.1 z.2 j i) ∧ ∀ ξ : Fin q → ℝ,
        lower * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a z.1 z.2 i j * ξ i * ξ j ∧
        ∑ i, ∑ j, a z.1 z.2 i j * ξ i * ξ j ≤ upper * ∑ i, ξ i ^ 2) :
    ∃ g, WeakSolutionEnergyInterface (G.horizontalFields hq) a I U u g := by
  obtain ⟨g, hg, hb, ht, he, _, _, _, _, _, hc⟩ :=
    hu.exists_zeroBoundary_weak_cutoff_time_witness G hq hqpos hw hspan a I U ha hlower hbound
  exact ⟨g, ⟨hg, hb, ht, he, hc⟩⟩

end HeatKernel
