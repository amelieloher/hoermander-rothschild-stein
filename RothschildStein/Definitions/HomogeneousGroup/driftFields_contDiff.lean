-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Provider.CanonicalFields

public import Mathlib.Analysis.Distribution.Distribution
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Data.List.FinRange
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Hormander.Interface.BasisVec

public import RothschildStein.Definitions.HomogeneousGroup.driftFields

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal NNReal
namespace RothschildStein

theorem HomogeneousGroup.driftFields_contDiff {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q + 1 ≤ N) (i : Fin (q + 1)) :
    ContDiff ℝ (⊤ : ℕ∞) (G.driftFields hq i) :=
  by exact RothschildStein.Provider.HomogeneousGroup.driftFields_contDiff G hq i

end RothschildStein
