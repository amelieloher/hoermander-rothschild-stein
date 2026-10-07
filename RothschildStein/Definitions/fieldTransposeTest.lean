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

public import RothschildStein.Definitions.testMultiplierOn

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal NNReal

namespace RothschildStein

def fieldTransposeTest {n : ℕ} (Ω : Opens (Fin n → ℝ))
    (V : (Fin n → ℝ) → (Fin n → ℝ))
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) V (Ω : Set (Fin n → ℝ)))
    (φ : TestFunction Ω ℝ (⊤ : ℕ∞)) : TestFunction Ω ℝ (⊤ : ℕ∞) :=
  -∑ j : Fin n, TestFunction.lineDerivCLM ℝ (Hormander.Interface.basisVec j)
    (testMultiplierOn Ω (fun x => V x j)
      ((contDiff_apply ℝ ℝ j).comp_contDiffOn hV) φ)

end RothschildStein
