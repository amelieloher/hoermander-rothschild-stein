-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G1.SmoothDependenceParameters
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators
namespace RothschildStein.L1

/-- The constant-coefficient combination defining canonical exponential coordinates. -/
def frameCoefficientField {d N : ℕ}
    (Y : Fin d → (Fin N → ℝ) → (Fin N → ℝ))
    (q : (Fin d → ℝ) × (Fin N → ℝ)) : Fin N → ℝ :=
  ∑ i, q.1 i • Y i q.2

/-- The tangent frame viewed as a continuous linear map in its coefficients. -/
def frameValueCLM {d N : ℕ}
    (Y : Fin d → (Fin N → ℝ) → (Fin N → ℝ)) (x : Fin N → ℝ) :
    (Fin d → ℝ) →L[ℝ] (Fin N → ℝ) :=
  ∑ i, (ContinuousLinearMap.proj i).smulRight (Y i x)

/-- Actual frame values are the coefficient map's values. -/
theorem frameValueCLM_apply {d N : ℕ}
    (Y : Fin d → (Fin N → ℝ) → (Fin N → ℝ)) (x : Fin N → ℝ) (u : Fin d → ℝ) :
    frameValueCLM Y x u = frameCoefficientField Y (u,x) := by
  simp only [frameValueCLM,frameCoefficientField,sum_apply,ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply]

/-- The canonical coefficient field vanishes for zero coefficients. -/
theorem frameCoefficientField_zero {d N : ℕ}
    (Y : Fin d → (Fin N → ℝ) → (Fin N → ℝ)) (x : Fin N → ℝ) :
    frameCoefficientField Y (0,x) = 0 := by
  simp only [frameCoefficientField,Pi.zero_apply,zero_smul,Finset.sum_const_zero]

/-- The canonical frame combination is jointly smooth in its
coefficients and point, on the coefficient cylinder (BB (10.15), p. 499). -/
theorem frameCoefficientField_contDiffOn {d N : ℕ} {Ω : Set (Fin N → ℝ)}
    (Y : Fin d → (Fin N → ℝ) → (Fin N → ℝ))
    (hY : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Y i) Ω) :
    ContDiffOn ℝ (⊤ : ℕ∞) (frameCoefficientField Y)
      ((univ : Set (Fin d → ℝ)) ×ˢ Ω) := by
  apply ContDiffOn.sum
  intro i _
  have hp : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : (Fin d → ℝ) × (Fin N → ℝ) => q.1 i)
      (univ ×ˢ Ω) :=
    ((ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ).contDiff.comp contDiff_fst).contDiffOn
  exact hp.smul ((hY i).comp contDiffOn_snd (fun _ h => h.2))
end RothschildStein.L1
