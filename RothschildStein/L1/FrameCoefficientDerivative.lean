-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.FrameCoefficientFields
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators
namespace RothschildStein.L1

/-- At zero coefficients the joint derivative of the actual
canonical coefficient field is exactly the tangent frame on the parameter
increment, and zero on the spatial increment (BB (10.15), p. 499). -/
theorem frameCoefficientField_hasFDerivAt_zero {d N : ℕ}
    (Y : Fin d → (Fin N → ℝ) → (Fin N → ℝ)) (x : Fin N → ℝ)
    (hY : ∀ i, DifferentiableAt ℝ (Y i) x) :
    HasFDerivAt (frameCoefficientField Y)
      ((frameValueCLM Y x).comp (ContinuousLinearMap.fst ℝ (Fin d → ℝ) (Fin N → ℝ))) (0,x) := by
  classical
  let L : Fin d → ((Fin d → ℝ) × (Fin N → ℝ)) →L[ℝ] ℝ :=
    fun i => (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ _ _)
  have hi : ∀ i, HasFDerivAt
      (fun q : (Fin d → ℝ) × (Fin N → ℝ) => q.1 i • Y i q.2)
      ((L i).smulRight (Y i x)) (0,x) := by
    intro i
    have hy : HasFDerivAt
        (fun q : (Fin d → ℝ) × (Fin N → ℝ) => Y i q.2)
        ((fderiv ℝ (Y i) x).comp (ContinuousLinearMap.snd ℝ (Fin d → ℝ) (Fin N → ℝ))) (0,x) :=
      (hY i).hasFDerivAt.comp (0,x) (ContinuousLinearMap.snd ℝ (Fin d → ℝ) (Fin N → ℝ)).hasFDerivAt
    have hh := (L i).hasFDerivAt.smul hy
    simpa [L] using hh
  have hs := HasFDerivAt.sum (u := Finset.univ) (fun i _ => hi i)
  have he : (∑ i, (L i).smulRight (Y i x)) =
      (frameValueCLM Y x).comp (ContinuousLinearMap.fst ℝ _ _) := by
    apply ContinuousLinearMap.ext
    intro q
    simp only [frameValueCLM,L,sum_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.proj_apply,
      ContinuousLinearMap.coe_fst']
  rw [he] at hs
  have hfun : (∑ i, fun q : (Fin d → ℝ) × (Fin N → ℝ) => q.1 i • Y i q.2) =
      frameCoefficientField Y := by
    funext q
    simp only [Finset.sum_apply,frameCoefficientField]
  rw [hfun] at hs
  exact hs
end RothschildStein.L1
