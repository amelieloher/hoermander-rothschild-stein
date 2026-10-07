-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.RegularizedPotentialDerivative
public import RothschildStein.H1.LocallyIntegrablePotentialDomain
public import RothschildStein.H1.ContinuousPuncturedCutoff
public import RothschildStein.H1.DilatedCutoffTest
public import RothschildStein.H1.FieldSubtractConstant

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter Topology MeasureTheory
namespace RothschildStein.H1
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- Step 1: the regularized potential field derivative is
exactly the regularized derivative-kernel potential minus the actual
compact-cutoff derivative term. -/
theorem StandingHypotheses.regularizedPotential_fieldDerivative_split
    (H : StandingHypotheses G q) (i : Fin (q + 1))
    {f η ψ : (Fin N → ℝ) → ℝ}
    (hf : ContDiffOn ℝ 1 f {(0 : Fin N → ℝ)}ᶜ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (heη : η =ᶠ[𝓝 (0 : Fin N → ℝ)] fun _ => 1)
    (hcψ : ContDiff ℝ 1 ψ) (hsψ : HasCompactSupport ψ) (ε : ℝ) :
    fieldDerivative (H.fields i) (G2.groupConvolution G ψ (fun w => f w * (1 - η (G.dilate ε⁻¹ w)))) =
      G2.groupConvolution G ψ (fun w => fieldDerivative (H.fields i) f w * (1 - η (G.dilate ε⁻¹ w))) -
        (fun x => ∫ w, f w * fieldDerivative (H.fields i) (η ∘ G.dilate ε⁻¹) w * ψ (G.mul x (G.inv w))) := by
  let ηs := η ∘ G.dilate ε⁻¹
  let θs := fun w => 1 - ηs w
  let F := fieldDerivative (H.fields i) f
  let A := fun w => F w * θs w
  let B := fun w => f w * fieldDerivative (H.fields i) ηs w
  have hηs : ContDiff ℝ (⊤ : ℕ∞) ηs := hη.comp (G2.contDiff_dilate G ε⁻¹)
  have hθs : ContDiff ℝ (⊤ : ℕ∞) θs := contDiff_const.sub hηs
  have heηs : ηs =ᶠ[𝓝 (0 : Fin N → ℝ)] fun _ => 1 := cutoff_comp_dilate_eventually_one G heη ε⁻¹
  have heθs : θs =ᶠ[𝓝 (0 : Fin N → ℝ)] fun _ => 0 := by
    filter_upwards [heηs] with w hw
    change 1 - ηs w = 0
    rw [hw, sub_self]
  have hF : ContinuousOn F {(0 : Fin N → ℝ)}ᶜ := by
    change ContinuousOn (fun w => fderiv ℝ f w (H.fields i w)) _
    exact (hf.continuousOn_fderiv_of_isOpen isOpen_compl_singleton (by norm_num)).clm_apply
      (H.fields_smooth G i).continuous.continuousOn
  have hA : LocallyIntegrable A volume :=
    (continuous_puncturedKernel_mul_cutoff hF hθs.continuous heθs).locallyIntegrable
  have hB : LocallyIntegrable B volume :=
    (continuous_puncturedKernel_mul_cutoff hf.continuousOn
      (smooth_fieldDerivative (H.fields i) (H.fields_smooth G i) ηs hηs).continuous
      (fieldDerivative_cutoff_eventually_zero (H.fields i) heηs)).locallyIntegrable
  have hdθ : fieldDerivative (H.fields i) θs = fun w => -fieldDerivative (H.fields i) ηs w :=
    fieldDerivative_one_sub_C1 (H.fields i) (hηs.of_le (by simp))
  have hk : (fun w => θs w * F w + f w * fieldDerivative (H.fields i) θs w) = A + (-B) := by
    funext w
    rw [hdθ]
    change θs w * F w + f w * (-fieldDerivative (H.fields i) ηs w) = F w * θs w + -(f w * fieldDerivative (H.fields i) ηs w)
    ring
  have h := H.fieldDerivative_regularizedPotential G i hf (hθs.of_le (by simp)) heθs hcψ hsψ
  change fieldDerivative (H.fields i) (G2.groupConvolution G ψ (fun w => f w * θs w)) =
    G2.groupConvolution G ψ (fun w => θs w * F w + f w * fieldDerivative (H.fields i) θs w) at h
  rw [hk, groupConvolution_add_localKernels G hA hB.neg hcψ.continuous hsψ] at h
  have hneg : G2.groupConvolution G ψ (-B) = -G2.groupConvolution G ψ B := by
    have he : -B = (-1 : ℝ) • B := by funext w; simp
    rw [he]
    funext x
    rw [G2.groupConvolution_smul_right]
    simp
  rw [hneg] at h
  have hraw : G2.groupConvolution G ψ B = fun x => ∫ w, B w * ψ (G.mul x (G.inv w)) := by
    funext x
    rw [G2.groupConvolution_def]
    apply integral_congr_ae
    exact Eventually.of_forall fun _ => mul_comm _ _
  rw [hraw] at h
  change fieldDerivative (H.fields i) (G2.groupConvolution G ψ (fun w => f w * θs w)) =
    G2.groupConvolution G ψ A - (fun x => ∫ w, B w * ψ (G.mul x (G.inv w)))
  simpa only [sub_eq_add_neg] using h

end RothschildStein.H1
