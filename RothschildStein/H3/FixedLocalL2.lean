-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.TransposeLocalSetting
public import RothschildStein.H2.DataDL2Certificate
public import RothschildStein.H2.SingularL2Adjoint

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set Metric MeasureTheory
open scoped ENNReal
variable {N : ℕ} (G : HomogeneousGroup N)

/-- The fixed local L2 operator is defined at exponent one half using
the local L2 extension theorem. -/
def fixedLocalL2Operator (ν : G2.HomogeneousNorm G)
    (h1 : ν.c = 1) (hsym : ν.Symmetric) (A S : ℝ)
    (K : ControlCarrier N → ControlCarrier N → ℝ)
    (H : letI := gaugeMetric G ν h1 hsym; TruncatedKernelFacts volume A S K)
    (Ht : letI := gaugeMetric G ν h1 hsym
      TruncatedKernelFacts volume A S (fun x y => K y x)) :
    letI := gaugeMetric G ν h1 hsym
    Lp ℝ 2 (volume.restrict (ball (0 : ControlCarrier N) 2)) →L[ℝ]
      Lp ℝ 2 (volume.restrict (ball (0 : ControlCarrier N) 2)) := by
  let := gaugeMetric G ν h1 hsym
  let P := localTransposeData_of_truncatedKernelFacts G ν h1 hsym A S K H Ht
  exact P.l2Operator realizationExponent_bounds.1
    realizationExponent_bounds.2 realizationExponent_bounds.2 realizationExponent_bounds.2
    realizationExponent_bounds.2 realizationExponent_bounds.2 realizationExponent_bounds.2

/-- The actual fixed transpose local L2 operator. -/
def fixedTransposeLocalL2Operator (ν : G2.HomogeneousNorm G)
    (h1 : ν.c = 1) (hsym : ν.Symmetric) (A S : ℝ)
    (K : ControlCarrier N → ControlCarrier N → ℝ)
    (H : letI := gaugeMetric G ν h1 hsym; TruncatedKernelFacts volume A S K)
    (Ht : letI := gaugeMetric G ν h1 hsym
      TruncatedKernelFacts volume A S (fun x y => K y x)) :
    letI := gaugeMetric G ν h1 hsym
    Lp ℝ 2 (volume.restrict (ball (0 : ControlCarrier N) 2)) →L[ℝ]
      Lp ℝ 2 (volume.restrict (ball (0 : ControlCarrier N) 2)) := by
  let := gaugeMetric G ν h1 hsym
  let P := localTransposeData_of_truncatedKernelFacts G ν h1 hsym A S K H Ht
  exact P.transposeL2Operator realizationExponent_bounds.1
    realizationExponent_bounds.2 realizationExponent_bounds.2 realizationExponent_bounds.2
    realizationExponent_bounds.2 realizationExponent_bounds.2 realizationExponent_bounds.2

/-- The fixed L2 operator pair satisfies the original and transpose
kernel bounds and full integral adjointness. -/
theorem fixedLocalL2_certificates_of_truncatedKernelFacts (ν : G2.HomogeneousNorm G)
    (h1 : ν.c = 1) (hsym : ν.Symmetric) (A S : ℝ)
    (K : ControlCarrier N → ControlCarrier N → ℝ)
    (H : letI := gaugeMetric G ν h1 hsym; TruncatedKernelFacts volume A S K)
    (Ht : letI := gaugeMetric G ν h1 hsym
      TruncatedKernelFacts volume A S (fun x y => K y x)) :
    letI := gaugeMetric G ν h1 hsym
    let Q := localKernelData_of_truncatedKernelFacts G ν h1 hsym A S K H
    let P := localTransposeData_of_truncatedKernelFacts G ν h1 hsym A S K H Ht
    let T := fixedLocalL2Operator G ν h1 hsym A S K H Ht
    let Ts := fixedTransposeLocalL2Operator G ν h1 hsym A S K H Ht
    H2.LocalL2Certificate (groupSetting G ν h1 hsym) 0 2 1 Q.singularA Q.singularS
      (P.l2Constant realizationExponent) Q.cutoffKernel T ∧
    H2.LocalL2Certificate (groupSetting G ν h1 hsym) 0 2 1 Q.singularA Q.singularS
      (P.l2Constant realizationExponent) (fun x y => Q.cutoffKernel y x) Ts ∧
    (∀ v w : Lp ℝ 2 (volume.restrict (ball (0 : ControlCarrier N) 2)),
      (∫ x, (T v) x * w x ∂volume.restrict (ball (0 : ControlCarrier N) 2)) =
        ∫ x, v x * (Ts w) x ∂volume.restrict (ball (0 : ControlCarrier N) 2)) := by
  let := gaugeMetric G ν h1 hsym
  let Q := localKernelData_of_truncatedKernelFacts G ν h1 hsym A S K H
  let P := localTransposeData_of_truncatedKernelFacts G ν h1 hsym A S K H Ht
  have hA : P.data.singularA = Q.singularA := rfl
  have hS : P.data.singularS = Q.singularS := rfl
  have ht := P.l2Certificate realizationExponent_bounds.1
    realizationExponent_bounds.2 realizationExponent_bounds.2 realizationExponent_bounds.2
    realizationExponent_bounds.2 realizationExponent_bounds.2 realizationExponent_bounds.2
  have hts := P.transposeL2Certificate realizationExponent_bounds.1
    realizationExponent_bounds.2 realizationExponent_bounds.2 realizationExponent_bounds.2
    realizationExponent_bounds.2 realizationExponent_bounds.2 realizationExponent_bounds.2
  have hminP : min P.data.β₀ P.data.β = 1 := by
    change min (1 : ℝ) 1 = 1
    exact min_self _
  have hminQ : min (localKernelData_of_truncatedKernelFacts G ν h1 hsym A S K H).β₀
      (localKernelData_of_truncatedKernelFacts G ν h1 hsym A S K H).β = 1 := by
    change min (1 : ℝ) 1 = 1
    exact min_self _
  refine ⟨?_, ?_, ?_⟩
  · have hh := ht
    simp only [hA, hS, hminP] at hh
    convert hh using 1 <;> rfl
  · have hh := hts
    simp only [hminQ] at hh
    convert hh using 1 <;> rfl
  · intro v w
    have he := P.l2Operator_adjoint realizationExponent_bounds.1
      realizationExponent_bounds.2 realizationExponent_bounds.2 realizationExponent_bounds.2
      realizationExponent_bounds.2 realizationExponent_bounds.2 realizationExponent_bounds.2 v w
    change inner ℝ ((fixedLocalL2Operator G ν h1 hsym A S K H Ht) v) w =
      inner ℝ v ((fixedTransposeLocalL2Operator G ν h1 hsym A S K H Ht) w) at he
    rw [L2.inner_def, L2.inner_def] at he
    simpa only [Real.inner_apply] using he

end RothschildStein.H3
