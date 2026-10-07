-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.ExponentEmbedding
public import RothschildStein.H2.SingularHolderOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set Metric MeasureTheory
open scoped NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- L2 embeddings of equal Holder representatives agree, even when
constructed at different exponents. -/
theorem holderL2_eq_of_function_eq {δ s : ℝ≥0} {U : Set X} {μ : Measure X}
    (hδ : 0 < δ) (hs : 0 < s) (hU : MeasurableSet U) (hμ : μ U < ⊤)
    (f : H2.holderFunctions δ U) (g : H2.holderFunctions s U)
    (he : (f : X → ℝ) = g) :
    H2.holderL2 δ U μ hδ hU hμ f = H2.holderL2 s U μ hs hU hμ g := by
  apply (MemLp.toLp_eq_toLp_iff
    (f.property.1.memLp_two hδ hU hμ) (g.property.1.memLp_two hs hU hμ)).mpr
  exact Filter.Eventually.of_forall (fun x => congrFun he x)

/-- The principal-value representative does not depend on the
Holder exponent used to package the same input function. -/
theorem principalValueHolder_function_eq {D : H2.LocDoubling X} {d : H2.TruncDist D}
    (Q : H2.LocalKernelData D d) {δ s : ℝ≥0}
    (hδ : 0 < δ) (hδ₀ : (δ : ℝ) < Q.β₀) (hδβ : (δ : ℝ) < Q.β) (hδν : (δ : ℝ) < Q.ν)
    (hs : 0 < s) (hs₀ : (s : ℝ) < Q.β₀) (hsβ : (s : ℝ) < Q.β) (hsν : (s : ℝ) < Q.ν)
    (f : H2.holderFunctions δ (ball Q.z Q.R))
    (g : H2.holderFunctions s (ball Q.z Q.R)) (he : (f : X → ℝ) = g) :
    (Q.principalValueHolderOperator hδ hδ₀ hδβ hδν f : X → ℝ) =
      (Q.principalValueHolderOperator hs hs₀ hsβ hsν g : X → ℝ) := by
  change (ball Q.z Q.R).indicator (Q.principalValue (f : X → ℝ)) =
    (ball Q.z Q.R).indicator (Q.principalValue (g : X → ℝ))
  rw [he]

end RothschildStein.H3
