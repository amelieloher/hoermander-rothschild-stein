-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingNoDriftBaseAlphabet
public import RothschildStein.Definitions.triangularLift
public import RothschildStein.P1.PaddingNoDriftSmoothness

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.P1

/-- Constant triangular coefficients for the actual added
coordinate diffusions; original fields have zero vertical coefficients. -/
def paddingNoDriftPolynomials (q n d : ℕ) :
    Fin (q + d) → Fin d → MvPolynomial (Fin (n + d)) ℝ :=
  Fin.addCases (fun _ _ => 0)
    (fun j l => MvPolynomial.C (if l = j then 1 else 0))

/-- The genuine padded system is exactly the triangular lift
of its projected base alphabet. This reuses P2's weak lift calculus
without adding zero generators to the free homogeneous model. -/
theorem paddingNoDriftVectorFields_eq_triangularLift {q n d : ℕ}
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)) :
    paddingNoDriftVectorFields (d := d) X =
      triangularLift (paddingNoDriftBaseAlphabet (d := d) X)
        (paddingNoDriftPolynomials q n d) := by
  funext i ξ
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · funext l
    refine Fin.addCases (fun j => ?_) (fun j => ?_) l <;>
      simp [paddingNoDriftVectorFields, triangularLift, paddingNoDriftBaseAlphabet,
        paddingNoDriftPolynomials, paddingBaseField, paddingBaseCLM, joinPoint]; rfl
  · funext l
    refine Fin.addCases (fun j => ?_) (fun j => ?_) l <;>
      simp [paddingNoDriftVectorFields, triangularLift, paddingNoDriftBaseAlphabet,
        paddingNoDriftPolynomials, paddingDiffusionField, Hormander.Interface.basisVec,
        Pi.single_apply, Fin.ext_iff]; omega

end RothschildStein.P1
