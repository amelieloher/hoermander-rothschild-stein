-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.Interface.EuclideanDivergence
public import Hormander.Interface.LieAlgebraSpansOn
public import Mathlib.Analysis.Distribution.Distribution
public import Mathlib.Analysis.ODE.Basic
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Data.PNat.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal


@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal NNReal

namespace RothschildStein

def holderSeminorm {n : ℕ}
    (d : (Fin n → ℝ) → (Fin n → ℝ) → ℝ≥0∞)
    (α : ℝ) (V : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) : ℝ≥0∞ :=
  sInf {C : ℝ≥0∞ | C < ⊤ ∧
    ∀ x ∈ V, ∀ y ∈ V, d x y < ⊤ →
      ENNReal.ofReal |f x - f y| ≤ C * (d x y) ^ α}

end RothschildStein
