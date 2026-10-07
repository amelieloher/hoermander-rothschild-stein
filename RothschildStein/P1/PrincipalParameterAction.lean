-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PrincipalParameterDerivative
public import RothschildStein.P1.PrincipalLeadingTypes
public import RothschildStein.P1.PrincipalModelKernel

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators
namespace RothschildStein.P1
variable {N : ℕ} {F : KernelFrame N}

/-- The existing parameter-differentiated
operator really differentiates the model kernel while holding u fixed.
No regularity at the pole is required for this parameter identity. -/
theorem PrincipalTerm.parameterDerivative_modelKernel (t : PrincipalTerm F)
    (v : (Fin N → ℝ) × (Fin N → ℝ)) (ξ η u : Fin N → ℝ) :
    (t.parameterDerivative v).modelKernel ξ η u =
      fderiv ℝ (fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
        t.modelKernel p.1 p.2 u) (ξ, η) v := by
  classical
  have hc (α : Fin N → ℕ) (hα : α ∈ t.indices) :
      Differentiable ℝ (fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
        (t.D p.1 p.2).coefficient α u) :=
    ((t.parameterCoefficients_joint_smooth α hα).comp
      (contDiff_id.prodMk contDiff_const)).differentiable (by simp)
  have he : (fun p : (Fin N → ℝ) × (Fin N → ℝ) => t.modelKernel p.1 p.2 u) =
      (fun p => ∑ α ∈ t.indices,
        (t.D p.1 p.2).coefficient α u * euclideanPartial α (F.pole t.star) u) := by
    funext p
    simp only [PrincipalTerm.modelKernel, SmoothDifferentialOperator.apply, t.indices_eq]
  rw [he]
  have hs := fderiv_fun_sum (A := fun α (p : (Fin N → ℝ) × (Fin N → ℝ)) =>
    (t.D p.1 p.2).coefficient α u * euclideanPartial α (F.pole t.star) u)
    (fun α hα => ((hc α hα) (ξ, η)).mul_const _)
  rw [hs]
  simp only [sum_apply, PrincipalTerm.modelKernel,
    SmoothDifferentialOperator.apply, PrincipalTerm.parameterDerivative]
  apply Finset.sum_congr rfl
  intro α hα
  change α ∈ t.indices at hα
  rw [parameterOperatorDerivative_coefficient (fun p => t.D p.1 p.2) t.indices
    (t.parameterCoefficients_joint_smooth) (ξ, η) v α hα u]
  have hm := fderiv_mul_const ((hc α hα) (ξ, η))
    (euclideanPartial α (F.pole t.star) u)
  rw [hm]
  simp only [smul_apply, smul_eq_mul]
  ring

end RothschildStein.P1
