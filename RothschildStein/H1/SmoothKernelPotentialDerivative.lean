-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.CompactParameterIntegral
public import RothschildStein.H1.PuncturedFieldInvariance
public import RothschildStein.H1.OperatorAlgebra
public import RothschildStein.G2.ConvolutionSubstitution
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
attribute [local irreducible] RothschildStein.HomogeneousGroup.inv RothschildStein.HomogeneousGroup.mul
open Set MeasureTheory
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Step 1: the actual invariant field derivative of a
potential with a globally C¹ kernel is the potential of its field
derivative. Compactness is required only of the smooth test. -/
theorem fieldDerivative_groupConvolution_C1
    {V : (Fin N → ℝ) → (Fin N → ℝ)} (hV : G2.IsLeftInvariantField G V)
    {f ψ : (Fin N → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    (hψ : ContDiff ℝ 1 ψ) (hs : HasCompactSupport ψ) (x : Fin N → ℝ) :
    fieldDerivative V (G2.groupConvolution G ψ f) x =
      G2.groupConvolution G ψ (fieldDerivative V f) x := by
  let Φ := fun p : (Fin N → ℝ) × (Fin N → ℝ) => ψ p.2 * f (G.mul (G.inv p.2) p.1)
  have hm : ContDiff ℝ 1 (fun p : (Fin N → ℝ) × (Fin N → ℝ) => G.mul (G.inv p.2) p.1) :=
    ((G2.contDiff_mul G).of_le (by simp)).comp
      ((((G2.contDiff_inv G).of_le (by simp)).comp contDiff_snd).prodMk contDiff_fst)
  have hΦ : ContDiff ℝ 1 Φ := (hψ.comp contDiff_snd).mul (hf.comp hm)
  let D := fun p => (fderiv ℝ Φ p).comp (ContinuousLinearMap.inl ℝ (Fin N → ℝ) (Fin N → ℝ))
  have hD : Continuous D := (hΦ.continuous_fderiv (by norm_num)).clm_comp continuous_const
  have hiD : IntegrableOn (fun y => D (x,y)) (tsupport ψ) volume :=
    (hD.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact hs.isCompact
  have hpot : G2.groupConvolution G ψ f = fun z => ∫ y in tsupport ψ, Φ (z,y) := by
    funext z
    rw [G2.groupConvolution_eq_integral]
    apply (setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => ?_)).symm
    change ψ y * f (G.mul (G.inv y) z) = 0
    rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
  have hder := hasFDerivAt_integral_compact_parameter hΦ hs.isCompact x
  rw [hpot]
  change fderiv ℝ (fun z => ∫ y in tsupport ψ, Φ (z,y)) x (V x) = _
  rw [hder.fderiv, ContinuousLinearMap.integral_apply hiD]
  have he (y : Fin N → ℝ) : D (x,y) (V x) = ψ y * fieldDerivative V f (G.mul (G.inv y) x) := by
    have hdf : HasFDerivAt Φ (fderiv ℝ Φ (x,y)) (x,y) :=
      (hΦ.differentiable (by norm_num)).differentiableAt.hasFDerivAt
    have hin : HasFDerivAt (fun z : Fin N → ℝ => (z,y))
        (ContinuousLinearMap.inl ℝ (Fin N → ℝ) (Fin N → ℝ)) x := by
      have he : (ContinuousLinearMap.id ℝ (Fin N → ℝ)).prod
          (0 : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)) =
          ContinuousLinearMap.inl ℝ (Fin N → ℝ) (Fin N → ℝ) := by
        exact ContinuousLinearMap.ext fun _ => rfl
      rw [← he]
      exact (hasFDerivAt_id x).prodMk (hasFDerivAt_const y x)
    have hp : HasFDerivAt (fun z => Φ (z,y)) (D (x,y)) x := by
      convert hdf.comp x hin using 1
      funext z
      rfl
    rw [← hp.fderiv]
    change fieldDerivative V (fun z => ψ y * f (G.mul (G.inv y) z)) x = _
    rw [fieldDerivative_const_mul]
    change ψ y * fieldDerivative V (f ∘ G.mul (G.inv y)) x = _
    rw [fieldDerivative_comp_leftTranslation_at G hV (G.inv y) x
      (hf.differentiable (by norm_num)).differentiableAt]
  change (∫ y in tsupport ψ, D (x,y) (V x)) = _
  simp_rw [he]
  rw [G2.groupConvolution_eq_integral]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro y hy
  rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]

end RothschildStein.H1
