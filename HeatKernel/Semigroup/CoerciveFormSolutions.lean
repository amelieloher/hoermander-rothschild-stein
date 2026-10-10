-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.InnerProductSpace.LaxMilgram
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # Coercive form solutions with a Hilbert inclusion

The adjoint inclusion supplies the Riesz right-hand side for the Lax–Milgram equivalence.
-/

@[expose] public section
noncomputable section
namespace HeatKernel
variable {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B) (j : V →L[ℝ] H)

/-- The solution map for a coercive form with a spatial right-hand side. -/
def coerciveFormSolution : H →L[ℝ] V :=
  hB.continuousLinearEquivOfBilin.symm.toContinuousLinearMap.comp j.adjoint

theorem coerciveFormSolution_apply (f : H) :
    coerciveFormSolution B hB j f = hB.continuousLinearEquivOfBilin.symm (j.adjoint f) := rfl

theorem coerciveFormSolution_equation (f : H) (v : V) :
    B (coerciveFormSolution B hB j f) v = inner ℝ f (j v) := by
  calc
    _ = inner ℝ (hB.continuousLinearEquivOfBilin (coerciveFormSolution B hB j f)) v :=
      (hB.continuousLinearEquivOfBilin_apply _ v).symm
    _ = inner ℝ (j.adjoint f) v := by
      rw [coerciveFormSolution_apply, hB.continuousLinearEquivOfBilin.apply_symm_apply]
    _ = _ := j.adjoint_inner_left v f

end HeatKernel
