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

def hasIntrinsicDeriv {n : ℕ} (V : Opens (Fin n → ℝ))
    (X : (Fin n → ℝ) → (Fin n → ℝ))
    (f g : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ x ∈ (V : Set (Fin n → ℝ)),
    (∃ γ : ℝ → (Fin n → ℝ), γ 0 = x ∧
      IsIntegralCurveAt γ (fun _ => X) 0 ∧
      ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ (V : Set (Fin n → ℝ))) ∧
    ∀ γ : ℝ → (Fin n → ℝ), γ 0 = x →
      IsIntegralCurveAt γ (fun _ => X) 0 →
      (∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ (V : Set (Fin n → ℝ))) →
      HasDerivAt (fun t => f (γ t)) (g x) 0

end RothschildStein
