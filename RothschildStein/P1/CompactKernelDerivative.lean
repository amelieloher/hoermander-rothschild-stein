-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.CompactKernelIntegral
public import RothschildStein.S.ClassicalWords
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.P1
variable {N : ℕ}

/-- For a jointly C¹ kernel, the output derivative passes through
integration over a fixed compact input set. -/
theorem compactKernelIntegral_output_fderiv
    (Φ : (Fin N → ℝ) × (Fin N → ℝ) → ℝ)
    (hΦ : ContDiff ℝ 1 Φ) (K : Set (Fin N → ℝ)) (hK : IsCompact K)
    (ξ v : Fin N → ℝ) :
    fderiv ℝ (fun x => ∫ η in K, Φ (x, η)) ξ v =
      ∫ η in K, fderiv ℝ (fun x => Φ (x, η)) ξ v := by
  let D : (Fin N → ℝ) × (Fin N → ℝ) → (Fin N → ℝ) →L[ℝ] ℝ :=
    fun q => (fderiv ℝ Φ q).comp (ContinuousLinearMap.inl ℝ (Fin N → ℝ) (Fin N → ℝ))
  have hD : Continuous D :=
    ((hΦ.fderiv_right (by simp) : ContDiff ℝ 0 (fderiv ℝ Φ)).clm_comp contDiff_const).continuous
  have hd : ∀ x η, HasFDerivAt (fun y => Φ (y, η)) (D (x, η)) x := by
    intro x η
    exact (hΦ.differentiable (by simp) (x, η)).hasFDerivAt.comp x
      (by simpa only [ContinuousLinearMap.inl_apply, Prod.mk_add_mk, zero_add, add_zero]
        using (ContinuousLinearMap.inl ℝ (Fin N → ℝ) (Fin N → ℝ)).hasFDerivAt.const_add (0, η))
  rw [(compactKernelIntegral_hasFDerivAt Φ D hΦ.continuous hD hd K hK ξ).fderiv]
  have hDi : IntegrableOn (fun η => D (ξ, η)) K volume :=
    (hD.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact hK
  rw [ContinuousLinearMap.integral_apply hDi]
  apply integral_congr_ae
  filter_upwards with η
  rw [(hd ξ η).fderiv]

/-- The compact kernel action has the actual weak output-field
 derivative supplied by its differentiated kernel. -/
theorem compactKernelIntegral_hasWeakFieldDeriv
    (Ω : TopologicalSpace.Opens (Fin N → ℝ))
    (X : Fin 1 → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin N → ℝ)))
    (Φ : (Fin N → ℝ) × (Fin N → ℝ) → ℝ)
    (hΦ : ContDiff ℝ 1 Φ) (K : Set (Fin N → ℝ)) (hK : IsCompact K) :
    hasWeakWordDeriv X Ω [0] (fun x => ∫ η in K, Φ (x, η))
      (fun x => ∫ η in K, fieldDerivative (X 0) (fun y => Φ (y, η)) x) := by
  have hf : ContDiff ℝ 1 (fun x => ∫ η in K, Φ (x, η)) :=
    compactKernelIntegral_contDiff_nat 1 Φ hΦ K hK
  have hw := S.hasWeakWordDeriv_classical_finite Ω X hX [0]
    (fun x => ∫ η in K, Φ (x, η)) (by simpa using hf.contDiffOn)
  have he : wordDerivative X [0] (fun x => ∫ η in K, Φ (x, η)) =
      (fun x => ∫ η in K, fieldDerivative (X 0) (fun y => Φ (y, η)) x) := by
    funext x
    exact compactKernelIntegral_output_fderiv Φ hΦ K hK x (X 0 x)
  rw [he] at hw
  exact hw

end RothschildStein.P1
