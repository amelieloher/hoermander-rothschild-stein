-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.GraphForm
public import HeatKernel.Form.CoefficientEnergy
import Mathlib.Tactic.Linter

/-! # Weak form operators and the nonpositive heat generator convention -/

@[expose] public section

noncomputable section

open Set MeasureTheory TopologicalSpace

namespace HeatKernel

/-- An L² vector represents the positive operator associated with a bilinear form when its
pairing with every domain vector is the form pairing. -/
def IsWeakFormOperatorValue {F H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (ι : F → H) (B : F → F → ℝ) (u : F) (g : H) : Prop :=
  ∀ v, B u v = inner ℝ g (ι v)

end HeatKernel
