-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.UniformFieldDerivativeLimit
public import RothschildStein.H1.RegularizedPotentialUniformLimit
public import RothschildStein.H1.RegularizedPotentialFieldSplit
public import RothschildStein.H1.CriticalFieldCutoffTerm
public import RothschildStein.H1.CriticalRegularizedPotentialLimit
public import RothschildStein.H1.HorizontalKernelPrincipalValue
public import RothschildStein.H1.HomogeneousFieldKernelRegularity
public import RothschildStein.G2.ConvolutionSmooth
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter Topology MeasureTheory
namespace RothschildStein.H1
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- The critical potential derivative is its actual
principal value plus the explicitly computed scalar cutoff term. -/
theorem StandingHypotheses.fieldDerivative_criticalPotential
    (H : StandingHypotheses G q) (i : Fin q)
    {f η ψ : (Fin N → ℝ) → ℝ} {R : ℝ}
    (hf : ContDiffOn ℝ 1 f {(0 : Fin N → ℝ)}ᶜ)
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 → f (G.dilate t x) = t ^ (1 - (G.homogeneousDimension : ℝ)) * f x)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hsη : HasCompactSupport η)
    (heη : η =ᶠ[𝓝 (0 : Fin N → ℝ)] fun _ => 1)
    (hR : 0 < R) (hηout : ∀ w, R ≤ H.norm w → η w = 0)
    (hbη : ∀ w, ‖η w‖ ≤ 1)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hsψ : HasCompactSupport ψ) :
    fieldDerivative (H.fields i.succ) (G2.groupConvolution G ψ f) =
      (fun x => principalValueConvolution G H.norm (fieldDerivative (H.fields i.succ) f) ψ x +
        ψ x * ((∫ v in {v | H.norm v ≤ R}, fieldDerivative (H.fields i.succ) f v * (1 - η v)) -
          (∫ v, f v * fieldDerivative (H.fields i.succ) η v))) := by
  obtain ⟨hF, hhF⟩ := H.horizontalKernel_regular G i hf hhom
  have hi : LocallyIntegrable f volume := locallyIntegrable_homogeneousKernel G
    H.norm.gauge hf.continuousOn hhom (by linarith)
  have hscale : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 →
      fieldDerivative (H.fields i.succ) f (G.dilate t x) =
        t ^ (-(G.homogeneousDimension : ℝ)) * fieldDerivative (H.fields i.succ) f x := by
    simpa only [show (1 - (G.homogeneousDimension : ℝ)) - 1 =
      -(G.homogeneousDimension : ℝ) by ring] using hhF
  have hcancel := H.vanishingShellIntegrals_fieldDerivative G i.succ H.norm.gauge hf (by simpa using hhom)
  have hcu (ε : ℝ) : ContDiff ℝ (⊤ : ℕ∞)
      (G2.groupConvolution G ψ (fun w => f w * (1 - η (G.dilate ε⁻¹ w)))) := by
    have hηs := hη.comp (G2.contDiff_dilate G ε⁻¹)
    have heηs := cutoff_comp_dilate_eventually_one G heη ε⁻¹
    have heθ : (fun w => 1 - η (G.dilate ε⁻¹ w)) =ᶠ[𝓝 (0 : Fin N → ℝ)] fun _ => 0 := by
      filter_upwards [heηs] with w hw
      change η (G.dilate ε⁻¹ w) = 1 at hw
      rw [hw, sub_self]
    have hcθ : ContDiff ℝ 1 (fun w => 1 - η (G.dilate ε⁻¹ w)) :=
      (contDiff_const.sub hηs).of_le (by simp)
    have hc := contDiff_puncturedKernel_mul_cutoff hf hcθ heθ
    exact G2.contDiff_groupConvolution_left G hψ hsψ hc.continuous.locallyIntegrable
  have htu := tendstoUniformly_regularizedPotential G H.norm.gauge hf.continuousOn hhom
    (by linarith) hη.continuous hR hηout hbη hψ.continuous hsψ
  have htF := tendstoUniformly_criticalRegularizedPotential G H.norm.gauge hF hscale hcancel
    hη.continuous heη hR hηout hbη (hψ.of_le (by simp)) hsψ
  have hV : G2.IsHomogeneousField G (H.fields i.succ) 1 := by
    simpa using H.homogeneous i.succ
  have htB := tendstoUniformly_criticalFieldCutoffTerm G
    (H.fields_smooth G i.succ) hV H.norm.gauge hf.continuousOn hhom hη hsη heη
    (hψ.of_le (by simp)) hsψ
  have htD := htF.sub htB
  have he : (fun ε => fieldDerivative (H.fields i.succ)
      (G2.groupConvolution G ψ (fun w => f w * (1 - η (G.dilate ε⁻¹ w))))) =
      (fun ε => G2.groupConvolution G ψ
        (fun w => fieldDerivative (H.fields i.succ) f w * (1 - η (G.dilate ε⁻¹ w))) -
        (fun x => ∫ w, f w * fieldDerivative (H.fields i.succ) (η ∘ G.dilate ε⁻¹) w * ψ (G.mul x (G.inv w)))) := by
    funext ε
    exact H.regularizedPotential_fieldDerivative_split G i.succ hf hη heη
      (hψ.of_le (by simp)) hsψ ε
  have heOuter : (fun ε => fieldDerivative (H.fields i.succ)
      (G2.groupConvolution G ψ (fun w => f w * (1 - η (G.dilate ε⁻¹ w))))) =
      (fun ε => G2.groupConvolution G ψ
        (fun w => fieldDerivative (H.fields i.succ) f w * (1 - η (G.dilate ε⁻¹ w)))) -
        (fun ε x => ∫ w, f w * fieldDerivative (H.fields i.succ) (η ∘ G.dilate ε⁻¹) w * ψ (G.mul x (G.inv w))) := by
    exact he
  rw [← heOuter] at htD
  have hcPV := (H.horizontalKernel_principalValue G i H.norm.gauge hf hhom
    (hψ.of_le (by simp)) hsψ).1
  have heLimit : (fun x => principalValueConvolution G H.norm (fieldDerivative (H.fields i.succ) f) ψ x +
      ψ x * (∫ v in {v | H.norm v ≤ R}, fieldDerivative (H.fields i.succ) f v * (1 - η v))) -
      (fun x => ψ x * (∫ v, f v * fieldDerivative (H.fields i.succ) η v)) =
      (fun x => principalValueConvolution G H.norm (fieldDerivative (H.fields i.succ) f) ψ x +
        ψ x * ((∫ v in {v | H.norm v ≤ R}, fieldDerivative (H.fields i.succ) f v * (1 - η v)) -
          (∫ v, f v * fieldDerivative (H.fields i.succ) η v))) := by
    funext x
    change principalValueConvolution G H.norm (fieldDerivative (H.fields i.succ) f) ψ x +
      ψ x * (∫ v in {v | H.norm v ≤ R}, fieldDerivative (H.fields i.succ) f v * (1 - η v)) -
      ψ x * (∫ v, f v * fieldDerivative (H.fields i.succ) η v) =
      principalValueConvolution G H.norm (fieldDerivative (H.fields i.succ) f) ψ x +
      ψ x * ((∫ v in {v | H.norm v ≤ R}, fieldDerivative (H.fields i.succ) f v * (1 - η v)) -
        (∫ v, f v * fieldDerivative (H.fields i.succ) η v))
    ring
  rw [heLimit] at htD
  exact H.fieldDerivative_eq_of_uniformLimits G i.succ
    (fun ε => (hcu ε).of_le (by simp))
    ((G2.contDiff_groupConvolution_left G hψ hsψ hi).of_le (by simp))
    (hcPV.add (hψ.continuous.mul continuous_const)) htu htD

end RothschildStein.H1
