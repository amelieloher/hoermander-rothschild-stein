-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingDriftBaseAlphabet
public import RothschildStein.Definitions.triangularLift
public import RothschildStein.P1.PaddingDomainSmoothness

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.P1

/-- Constant triangular coefficients for diffusion padding
with the drift unchanged at index zero. -/
def paddingDriftPolynomials (q n d : ℕ) :
    Fin (q + d + 1) → Fin d → MvPolynomial (Fin (n + d)) ℝ :=
  Fin.cases (fun _ => 0) (Fin.addCases (fun _ _ => 0)
    (fun j l => MvPolynomial.C (if l = j then 1 else 0)))

/-- The actual drift-padded system equals the triangular lift
of its projected alphabet. Only appended fields have vertical components. -/
theorem paddingVectorFields_eq_triangularLift {q n d : ℕ}
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)) :
    paddingVectorFields (d := d) X =
      triangularLift (paddingDriftBaseAlphabet (d := d) X)
        (paddingDriftPolynomials q n d) := by
  funext i ξ
  refine Fin.cases ?_ (fun a => ?_) i
  · funext l
    refine Fin.addCases (fun j => ?_) (fun j => ?_) l <;>
      (simp [paddingVectorFields, triangularLift, paddingDriftBaseAlphabet,
        paddingDriftPolynomials, paddingBaseField, paddingBaseCLM, joinPoint] <;> rfl)
  · refine Fin.addCases (fun a => ?_) (fun b => ?_) a
    · funext l
      refine Fin.addCases (fun j => ?_) (fun j => ?_) l <;>
        (simp [paddingVectorFields, triangularLift, paddingDriftBaseAlphabet,
          paddingDriftPolynomials, paddingBaseField, paddingBaseCLM, joinPoint] <;> rfl)
    · funext l
      refine Fin.addCases (fun j => ?_) (fun j => ?_) l <;>
        (simp [paddingVectorFields, triangularLift, paddingDriftBaseAlphabet,
          paddingDriftPolynomials, paddingDiffusionField, Hormander.Interface.basisVec,
          Pi.single_apply, Fin.ext_iff] <;> omega)

end RothschildStein.P1
