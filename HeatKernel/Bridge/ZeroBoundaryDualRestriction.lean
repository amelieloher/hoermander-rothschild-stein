-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.ZeroBoundary
public import HeatKernel.Bridge.DualPrecomposition
import Mathlib.Tactic.Linter
import all Mathlib.Analysis.Normed.Operator.Basic

/-! # Restricting continuous form functionals to zero-boundary domains -/

@[expose] public section
noncomputable section
open TopologicalSpace MeasureTheory
namespace HeatKernel

variable {N q : ℕ} (V : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))

/-- The zero-boundary form domain includes continuously into the global form domain. -/
def zeroBoundaryEnergyInclusion : zeroBoundaryGraph V X →L[ℝ] energyGraph (N := N) ⊤ X :=
  (zeroBoundaryGraph V X).subtypeL.codRestrict (energyGraph ⊤ X)
    (fun v => zeroBoundaryGraph_le_energyGraph V X v.property)

/-- Restriction of a global form functional to a zero-boundary form domain is bounded linear. -/
def zeroBoundaryDualRestriction :
    (energyGraph (N := N) ⊤ X →L[ℝ] ℝ) →L[ℝ] (zeroBoundaryGraph V X →L[ℝ] ℝ) :=
  dualPrecomposition (zeroBoundaryEnergyInclusion V X)

/-- Dual restriction acts by evaluating on the included form test. -/
theorem zeroBoundaryDualRestriction_apply (F : energyGraph (N := N) ⊤ X →L[ℝ] ℝ)
    (v : zeroBoundaryGraph V X) :
    zeroBoundaryDualRestriction V X F v =
      F ⟨v, zeroBoundaryGraph_le_energyGraph V X v.property⟩ := rfl

/-- Dual restriction preserves Bochner L² membership. -/
theorem memLp_zeroBoundaryDualRestriction {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {F : α → (energyGraph (N := N) ⊤ X →L[ℝ] ℝ)}
    (hF : MemLp F 2 μ) : MemLp (fun t => zeroBoundaryDualRestriction V X (F t)) 2 μ :=
  memLp_dualPrecomposition (zeroBoundaryEnergyInclusion V X) hF

end HeatKernel
