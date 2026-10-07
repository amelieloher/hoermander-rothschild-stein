-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingCoordinates
public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Topology.Algebra.Module.Determinant

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace RothschildStein.L1

/-- Changing both input and output carriers by the same linear
coordinate equivalence preserves the full chart Jacobian. -/
theorem det_fderiv_conjugate {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃L[ℝ] F) (f : E → E) (q : F)
    (hf : DifferentiableAt ℝ f (e.symm q)) :
    (fderiv ℝ (fun p => e (f (e.symm p))) q).det =
      (fderiv ℝ f (e.symm q)).det := by
  have hd : HasFDerivAt (fun p => e (f (e.symm p)))
      ((e : E →L[ℝ] F).comp ((fderiv ℝ f (e.symm q)).comp (e.symm : F →L[ℝ] E))) q :=
    e.hasFDerivAt.comp q (hf.hasFDerivAt.comp q e.symm.hasFDerivAt)
  rw [hd.fderiv]
  exact LinearMap.det_conj (fderiv ℝ f (e.symm q)).toLinearMap e.toLinearEquiv

/-- The actual full lifted chart determinant transfers from the
joined coordinates to the product carrier used in the fiber
change-of-variables proof (BB pp. 520–521, (10.49)). -/
theorem abs_det_fderiv_padding_chart {n m : ℕ}
    (f : (Fin (n+m) → ℝ) → (Fin (n+m) → ℝ))
    (q : (Fin n → ℝ) × (Fin m → ℝ))
    (hf : DifferentiableAt ℝ f ((P1.paddingCoordinates n m).symm q)) :
    |(fderiv ℝ (fun p => P1.paddingCoordinates n m
      (f ((P1.paddingCoordinates n m).symm p))) q).det| =
      |(fderiv ℝ f ((P1.paddingCoordinates n m).symm q)).det| :=
  congrArg abs (det_fderiv_conjugate (P1.paddingCoordinates n m) f q hf)

end RothschildStein.L1
