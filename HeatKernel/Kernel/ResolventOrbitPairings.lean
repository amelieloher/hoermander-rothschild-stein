-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Semigroup.InverseResolventGraph
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-! # Orbit pairings from a symmetric resolvent graph

An orbit derivative and a test Laplacian represented in the same
self-adjoint inverse-resolvent graph give the weak generator pairing.
-/

@[expose] public section

noncomputable section

namespace HeatKernel

/-- Two graph relations with the heat-generator sign give the weak orbit pairing. -/
theorem inner_orbit_derivative_test_eq_of_resolvent_graph {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (R : H →L[ℝ] H) (hR : IsSelfAdjoint R) {u du φ ψ : H}
    (hu : InverseResolventGraph R u (-du))
    (hφ : InverseResolventGraph R φ (-ψ)) :
    inner ℝ du φ = inner ℝ u ψ := by
  have h := inverseResolventGraph_symm R hR hu hφ
  simp only [inner_neg_left, inner_neg_right] at h
  exact neg_inj.mp h

end HeatKernel
