-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.TwoFlowFiniteExponentialBound
public import RothschildStein.G3.DilatedLieFiniteExponentialBound
public import RothschildStein.G3.ModelProduct
public import RothschildStein.G3.ModelWords
public import RothschildStein.G3.LinearWordPolynomials
public import RothschildStein.G3.FiniteLieFieldDilation
public import RothschildStein.G3.ExponentialFlowSmoothBase
public import RothschildStein.G3.LinearFieldEvaluation
public import RothschildStein.G3.CompactWordJetBounds
public import RothschildStein.G3.BasisWordUniformJets
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped BigOperators
namespace RothschildStein.G3

def primitiveWordJetBudget {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (R : ℕ) (B : ℝ) : ℝ :=
  ∑ j, (2 ^ (R+1)) ^ ((modelBasisWord D j).length-1) * B ^ (modelBasisWord D j).length

end RothschildStein.G3
