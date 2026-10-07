-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.OffDiagonalExtension

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal NNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {D : LocDoubling X} {d : TruncDist D}

/-- Transport the extension representation to an explicitly
identified integration patch, avoiding any change to its L² domain. -/
theorem LocalKernelData.offDiagonal_on_of_holder_formula (Q : LocalKernelData D d)
    {U : Set X} (hU : U = ball Q.z Q.R) (hUm : MeasurableSet U) (hμ : D.μ U < ⊤)
    {δ : ℝ≥0} (hδ : 0 < δ) (hδ₁ : δ ≤ 1)
    (S : Lp ℝ 2 (D.μ.restrict U) →L[ℝ] Lp ℝ 2 (D.μ.restrict U))
    (hS : ∀ f : holderFunctions δ U,
      (S (holderL2 δ U D.μ hδ hUm hμ f) : X → ℝ) =ᵐ[D.μ.restrict U] Q.principalValue f) :
    OffDiagonalL2 D U Q.cutoffKernel S := by
  subst U
  exact Q.offDiagonal_of_holder_formula hδ hδ₁ S hS

end RothschildStein.H2
