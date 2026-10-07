-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.Distribution.Distribution
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Data.List.FinRange
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Hormander.Interface.BasisVec

public import RothschildStein.Definitions.HomogeneousGroup.mul
public import RothschildStein.Definitions.HomogeneousGroup.inv

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal NNReal
namespace RothschildStein

def HomogeneousGroup.HasPrincipalValue {N : ℕ} (G : HomogeneousGroup N)
    (ν kernel f : (Fin N → ℝ) → ℝ) (v : Fin N → ℝ) (value : ℝ) : Prop :=
  (∀ ε : ℝ, 0 < ε →
    IntegrableOn (fun u => f u * kernel (G.mul (G.inv u) v))
      {u | ε < ν (G.mul (G.inv u) v)} volume) ∧
  Filter.Tendsto
    (fun ε : ℝ => ∫ u in {u | ε < ν (G.mul (G.inv u) v)},
      f u * kernel (G.mul (G.inv u) v))
    (nhdsWithin 0 (Ioi 0)) (nhds value)

end RothschildStein
