-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.LocalKernelSetting
public import RothschildStein.H2.TransposeData

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open MeasureTheory
open scoped NNReal
variable {N : ℕ} (G : HomogeneousGroup N)

/-- The original and reflected truncated-kernel bounds give the
transposed local setting with identical cutoffs and zero fractional pieces
(BB proof of Theorem 8.22, pp. 357–359). -/
def localTransposeData_of_truncatedKernelFacts (ν : G2.HomogeneousNorm G)
    (h1 : ν.c = 1) (hsym : ν.Symmetric) (A S : ℝ)
    (K : ControlCarrier N → ControlCarrier N → ℝ)
    (H : letI := gaugeMetric G ν h1 hsym
      TruncatedKernelFacts volume A S K)
    (Ht : letI := gaugeMetric G ν h1 hsym
      TruncatedKernelFacts volume A S (fun x y => K y x)) :
    letI := gaugeMetric G ν h1 hsym
    H2.TransposeData (localKernelData_of_truncatedKernelFacts G ν h1 hsym A S K H) := by
  let := gaugeMetric G ν h1 hsym
  exact {
    data := localKernelData_of_truncatedKernelFacts G ν h1 hsym A S (fun x y => K y x) Ht
    centre := rfl
    radius := rfl
    supportRadius := rfl
    outerCutoff := rfl
    innerCutoff := rfl
    transpose := fun _ _ _ _ => rfl
  }

/-- The fixed exponent used to construct the operator is one half.
All subsequent Holder exponents refer to this same operator. -/
def realizationExponent : ℝ≥0 := 1 / 2

/-- The fixed construction exponent lies strictly between zero and one. -/
theorem realizationExponent_bounds :
    0 < realizationExponent ∧ (realizationExponent : ℝ) < 1 := by
  norm_num [realizationExponent]

end RothschildStein.H3
