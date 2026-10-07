-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ParameterOperatorDerivative
public import RothschildStein.P1.TypeKernel

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.P1.PrincipalTerm
variable {N : ℕ} {F : KernelFrame N}

/-- Joint coefficient smoothness in the paired
parameter carrier and group coordinates. -/
theorem parameterCoefficients_joint_smooth (t : PrincipalTerm F)
    (a : Fin N → ℕ) (ha : a ∈ t.indices) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun z : ((Fin N → ℝ) × (Fin N → ℝ)) × (Fin N → ℝ) =>
        (t.D z.1.1 z.1.2).coefficient a z.2) :=
  (t.coefficient_smooth a ha).comp
    ((contDiff_fst.fst).prodMk ((contDiff_fst.snd).prodMk contDiff_snd))

/-- A parameter derivative of a principal
operator family is a principal term of the same degree, with jointly
smooth coefficients. Both endpoints are covered by the pair direction;
the external cutoffs and pole are held fixed (BB Rem 11.9, p. 544). -/
def parameterDerivative (t : PrincipalTerm F)
    (v : (Fin N → ℝ) × (Fin N → ℝ)) : PrincipalTerm F where
  a := t.a
  b := t.b
  D := fun ξ η => parameterOperatorDerivative (fun p => t.D p.1 p.2) t.indices
    (parameterCoefficients_joint_smooth t) (ξ, η) v
  indices := t.indices
  indices_eq := by intro ξ η; rfl
  coefficient_smooth := by
    intro a ha
    have h := parameterOperatorDerivative_joint_smooth
      (fun p : (Fin N → ℝ) × (Fin N → ℝ) => t.D p.1 p.2) t.indices
      (parameterCoefficients_joint_smooth t) v a ha
    exact h.comp ((contDiff_fst.prodMk contDiff_snd.fst).prodMk contDiff_snd.snd)
  degree := t.degree
  homogeneous := fun ξ η => parameterOperatorDerivative_homogeneous F.G
    (fun p : (Fin N → ℝ) × (Fin N → ℝ) => t.D p.1 p.2) t.indices
    (fun p => t.indices_eq p.1 p.2) (parameterCoefficients_joint_smooth t)
    t.degree (fun p => t.homogeneous p.1 p.2) (ξ, η) v
  star := t.star

end RothschildStein.P1.PrincipalTerm
