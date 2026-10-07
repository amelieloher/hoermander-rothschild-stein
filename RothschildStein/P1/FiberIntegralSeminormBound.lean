-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.FiberIntegralSmoothness
public import RothschildStein.P1.FiberIntegralMassBound
public import RothschildStein.P1.FiberDerivativeNorm

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.P1

/-- Every derivative seminorm of fiber integration is bounded
by the same input seminorm times the volume of a fixed fiber support. -/
theorem norm_iteratedFDeriv_fiberIntegral_le {n d : ℕ} {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
    {F : ((Fin n → ℝ) × (Fin d → ℝ)) → B}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F)
    {K : Set (Fin d → ℝ)} (hK : IsCompact K)
    (hsupp : tsupport F ⊆ Prod.snd ⁻¹' K) (m : ℕ) {C : ℝ}
    (hbound : ∀ p, ‖iteratedFDeriv ℝ m F p‖ ≤ C) (x : Fin n → ℝ) :
    ‖iteratedFDeriv ℝ m (fun y => ∫ z, F (y, z)) x‖ ≤ volume.real K * C := by
  induction m generalizing B with
  | zero =>
      rw [norm_iteratedFDeriv_zero]
      apply norm_fiberIntegral_le hK
      · intro y z hz
        apply image_eq_zero_of_notMem_tsupport
        exact fun hp => hz (hsupp hp)
      · intro y z _
        simpa only [norm_iteratedFDeriv_zero] using hbound (y, z)
  | succ m ih =>
      let D : ((Fin n → ℝ) × (Fin d → ℝ)) → ((Fin n → ℝ) →L[ℝ] B) :=
        fun p => (fderiv ℝ F p).comp
          (ContinuousLinearMap.inl ℝ (Fin n → ℝ) (Fin d → ℝ))
      have hD : ContDiff ℝ (⊤ : ℕ∞) D :=
        (contDiff_infty_iff_fderiv.mp hF).2.clm_comp contDiff_const
      have hDc : HasCompactSupport D :=
        (hFc.fderiv ℝ).comp_left
          (g := fun L : ((Fin n → ℝ) × (Fin d → ℝ)) →L[ℝ] B => L.comp
            (ContinuousLinearMap.inl ℝ (Fin n → ℝ) (Fin d → ℝ))) (by simp)
      have hDsupp : tsupport D ⊆ Prod.snd ⁻¹' K := by
        apply Subset.trans _ hsupp
        apply Subset.trans _ (tsupport_fderiv_subset ℝ)
        exact tsupport_comp_subset (g := fun L : ((Fin n → ℝ) × (Fin d → ℝ)) →L[ℝ] B =>
          L.comp (ContinuousLinearMap.inl ℝ (Fin n → ℝ) (Fin d → ℝ))) (by simp) _
      have hDbound : ∀ p, ‖iteratedFDeriv ℝ m D p‖ ≤ C := fun p =>
        (norm_iteratedFDeriv_baseDifferential_le hF m p).trans (hbound p)
      have he : fderiv ℝ (fun y => ∫ z, F (y, z)) =
          fun y => ∫ z, D (y, z) := funext fun y =>
        (hasFDerivAt_fiberIntegral (hF.of_le (by simp)) hFc y).fderiv
      rw [← norm_iteratedFDeriv_fderiv, he]
      exact ih hD hDc hDsupp hDbound

end RothschildStein.P1
