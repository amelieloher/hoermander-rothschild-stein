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

def isControlledCurve {m n : ℕ} (Ω : Set (Fin n → ℝ))
    (w : Fin m → ℕ+) (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (δ : ℝ) (γ : ℝ → (Fin n → ℝ)) : Prop :=
  0 < δ ∧ AbsolutelyContinuousOnInterval γ 0 1 ∧
  MapsTo γ (Icc 0 1) Ω ∧
  ∃ a : Fin m → ℝ → ℝ,
    (∀ i, AEMeasurable (a i) (volume.restrict (Icc (0 : ℝ) 1))) ∧
    ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)),
      (∀ i, |a i t| ≤ δ ^ (w i : ℕ)) ∧
      HasDerivAt γ (∑ i, a i t • X i (γ t)) t

end RothschildStein
