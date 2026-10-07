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

public import RothschildStein.Definitions.wordTranspose

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal NNReal

namespace RothschildStein

def hasWeakWordDeriv {m n : ℕ}
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (V : Opens (Fin n → ℝ)) (I : List (Fin m))
    (f g : (Fin n → ℝ) → ℝ) : Prop :=
  LocallyIntegrableOn f (V : Set (Fin n → ℝ)) volume ∧
  LocallyIntegrableOn g (V : Set (Fin n → ℝ)) volume ∧
  ∀ φ : TestFunction V ℝ (⊤ : ℕ∞),
    (∫ x in (V : Set (Fin n → ℝ)), g x * φ x) =
    ∫ x in (V : Set (Fin n → ℝ)), f x * wordTranspose X I φ x

end RothschildStein
