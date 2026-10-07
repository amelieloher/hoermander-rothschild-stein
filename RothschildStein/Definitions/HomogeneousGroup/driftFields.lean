-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.Distribution.Distribution
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Data.List.FinRange
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Hormander.Interface.BasisVec

public import RothschildStein.Definitions.HomogeneousGroup.canonicalField

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal NNReal
namespace RothschildStein

def HomogeneousGroup.driftFields {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q + 1 ≤ N) : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ) :=
  Fin.cases (G.canonicalField ⟨q, lt_of_lt_of_le (Nat.lt_succ_self q) hq⟩)
    (fun i : Fin q => G.canonicalField
      ⟨i.val, lt_of_lt_of_le (Nat.lt_succ_of_lt i.isLt) hq⟩)

end RothschildStein
