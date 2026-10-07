-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.Distribution.Distribution
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Data.List.FinRange
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Hormander.Interface.BasisVec


set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal NNReal
namespace RothschildStein

def isFundamentalDistribution {N : ℕ}
    (transposeOperator : (((Fin N → ℝ) → ℝ) → ((Fin N → ℝ) → ℝ)))
    (T : Distribution (⊤ : TopologicalSpace.Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞)) : Prop :=
  ∀ φ : TestFunction (⊤ : TopologicalSpace.Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞),
    ∃ ψ : TestFunction (⊤ : TopologicalSpace.Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞),
      (∀ x, ψ x = transposeOperator φ x) ∧ T ψ = φ 0

end RothschildStein
