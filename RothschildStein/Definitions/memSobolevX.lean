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

public import RothschildStein.Definitions.wordFamily
public import RothschildStein.Definitions.hasWeakWordDeriv

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal NNReal

namespace RothschildStein

def memSobolevX {m n : ℕ} (w : Fin m → ℕ+)
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (V : Opens (Fin n → ℝ)) (k : ℕ) (p : ℝ≥0∞)
    (f : (Fin n → ℝ) → ℝ) : Prop :=
  MemLp f p (volume.restrict (V : Set (Fin n → ℝ))) ∧
  ∀ I ∈ wordFamily w k, ∃ g : (Fin n → ℝ) → ℝ,
    hasWeakWordDeriv X V I f g ∧
    MemLp g p (volume.restrict (V : Set (Fin n → ℝ)))

end RothschildStein
