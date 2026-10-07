-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PrincipalTransferErrorKernel
public import RothschildStein.P1.TransferKernelChainRule
public import RothschildStein.P1.KernelFiberDerivatives

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MvPolynomial
open scoped BigOperators
namespace RothschildStein.P1.LiftedChart
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  (C : LiftedChart w s Ω hΩ X x₀ m) (F : KernelFrame (n+m))

/-- The constructed principal error is exactly
the output derivative plus the full input formal-adjoint correction,
off the diagonal. This establishes the kernel identity before taking
any cutoff limit (BB (11.36)–(11.37), pp. 555–556). -/
theorem principalTransferErrorKernel_eq (hF : C.IsLiftedFrame F) (t : PrincipalTerm F)
    (i : Fin k) {ξ η : Fin (n+m) → ℝ} (hξ : ξ ∈ C.U) (hη : η ∈ C.U) (hne : ξ ≠ η) :
    C.principalTransferErrorKernel F hF t i ξ η =
      fieldDerivative (C.Xl i) (fun ζ => t.kernel ζ η) ξ +
        ∑ j, fieldDerivative (wordBracket C.Xl (C.B j))
          (fun ζ => C.generatorTransferKernel F i j t.kernel ξ ζ) η +
        ∑ j, Hormander.Interface.euclideanDivergence (wordBracket C.Xl (C.B j)) η *
          C.generatorTransferKernel F i j t.kernel ξ η := by
  classical
  have hΓ := hF.pole_smooth t.star
  have hΨ : ContDiffOn ℝ 1 (kernelUncurry t.modelKernel) {z | z.2.2 ≠ 0} :=
    (t.modelKernel_contDiffOn hΓ).of_le (by simp)
  have hu : C.Θ η ξ ≠ 0 := (C.theta_eq_zero_iff hη hξ).not.mpr hne
  let p := fun j => eval (C.Θ η ξ) (C.generatorTransferCoefficient i j)
  let dout := fieldDerivative (C.Xl i) (fun ζ => t.modelKernel ζ η (C.Θ η ζ)) ξ
  let din := fun j => fieldDerivative (wordBracket C.Xl (C.B j))
    (fun ζ => t.modelKernel ξ ζ (C.Θ ζ ξ)) η
  let aout := (t.cutoffDerivative (C.Xl i) (C.transferGenerator_smooth F hF i)).kernel ξ η
  let ain := fun j => (t.inputCutoffDerivative (wordBracket C.Xl (C.B j))
    (C.transferBasis_smooth F hF j)).kernel ξ η
  have hdout := C.hasFDerivAt_kernel hΨ hη hξ hne
  have hdin := C.hasFDerivAt_transfer_input_kernel hΨ hξ hη hne
  have hout : fieldDerivative (C.Xl i) (fun ζ => t.kernel ζ η) ξ =
      aout + t.a ξ * t.b η * dout := by
    have hp := (((t.a.contDiff.differentiable (by simp) ξ).hasFDerivAt).mul_const (t.b η)).mul hdout
    simp only [Pi.mul_def] at hp
    have he : (fun ζ => t.kernel ζ η) =
        fun ζ => t.a ζ * t.b η * t.modelKernel ζ η (C.Θ η ζ) := by
      funext ζ; simp only [PrincipalTerm.kernel, PrincipalTerm.modelKernel, hF.Θ_eq]
    rw [he]
    simp only [aout, dout, PrincipalTerm.cutoffDerivative_kernel, fieldDerivative, hp.fderiv,
      add_apply, smul_apply, smul_eq_mul, hdout.fderiv, hF.Θ_eq]
    ring
  have hin (j : Fin (n+m)) :
      fieldDerivative (wordBracket C.Xl (C.B j)) (fun ζ => t.kernel ξ ζ) η =
        ain j + t.a ξ * t.b η * din j := by
    have hp := (((t.b.contDiff.differentiable (by simp) η).hasFDerivAt).const_mul (t.a ξ)).mul hdin
    simp only [Pi.mul_def] at hp
    have he : (fun ζ => t.kernel ξ ζ) =
        fun ζ => t.a ξ * t.b ζ * t.modelKernel ξ ζ (C.Θ ζ ξ) := by
      funext ζ; simp only [PrincipalTerm.kernel, PrincipalTerm.modelKernel, hF.Θ_eq]
    rw [he]
    simp only [ain, din, PrincipalTerm.inputCutoffDerivative_kernel, fieldDerivative, hp.fderiv,
      add_apply, smul_apply, smul_eq_mul, hdin.fderiv, hF.Θ_eq]
    ring
  have htransfer := C.transfer_kernel_chain_rule_split hΨ i hξ hη hne
  rw [kernelUncurry_fderiv_parameter t.modelKernel hΨ ξ η (C.Θ η ξ) (C.Xl i ξ) 0 hu,
    kernelUncurry_fderiv_model t.modelKernel hΨ ξ η (C.Θ η ξ)
      (C.generatorTransferRemainder i ξ η (C.Θ η ξ)) hu] at htransfer
  simp_rw [kernelUncurry_fderiv_parameter t.modelKernel hΨ ξ η (C.Θ η ξ) 0
    (wordBracket C.Xl (C.B _) η) hu] at htransfer
  have herr : (∑ l, C.generatorTransferRemainder i ξ η (F.Θ η ξ) l *
      t.leadingKernel (fun _ => Pi.single l 1) contDiff_const (F.G.weight l : ℤ)
        (coordinateField_homogeneous F.G l) ξ η) =
      t.a ξ * t.b η * fieldDerivative (C.generatorTransferRemainder i ξ η)
        (t.modelKernel ξ η) (C.Θ η ξ) := by
    simp_rw [PrincipalTerm.leadingKernel_eq t (fun _ => Pi.single _ 1) contDiff_const _
      (coordinateField_homogeneous F.G _) hΓ ξ η (by rw [hF.Θ_eq]; exact hu)]
    rw [fieldDerivative_coordinate_sum]
    simp only [fieldDerivative, hF.Θ_eq, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    ring
  have hdP (j : Fin (n+m)) : DifferentiableAt ℝ
      (fun ζ => eval (F.Θ ζ ξ) (C.generatorTransferCoefficient i j)) η := by
    rw [hF.Θ_eq]
    exact (((C.transferEndpointCoefficient_smooth i j).contDiffAt
      ((C.isOpen_U.prod C.isOpen_U).mem_nhds (show (ξ, η) ∈ C.U ×ˢ C.U from ⟨hξ, hη⟩))).differentiableAt
      (by simp)).comp η (differentiableAt_const ξ |>.prodMk differentiableAt_id)
  have hdK : DifferentiableAt ℝ (fun ζ => t.kernel ξ ζ) η := by
    have hp := (((t.b.contDiff.differentiable (by simp) η).hasFDerivAt).const_mul (t.a ξ)).mul hdin
    simpa only [Pi.mul_def, PrincipalTerm.kernel, PrincipalTerm.modelKernel, hF.Θ_eq] using hp.differentiableAt
  unfold principalTransferErrorKernel
  rw [herr, PrincipalTerm.endpointKernel_eq]
  simp_rw [PrincipalTerm.inputEndpointKernel_eq, C.transferIbpCoefficient_eq i _ hξ hη]
  simp only [generatorTransferKernel]
  simp_rw [S.fieldDerivative_mul _ _ _ η (hdP _) hdK, hin]
  simp only [hF.Θ_eq]
  rw [hout]
  change dout + ∑ j, p j * din j = _ at htransfer
  have hscaled := congrArg (fun z : ℝ => t.a ξ * t.b η * z) htransfer
  simp only [mul_add, Finset.mul_sum] at hscaled
  simp only [mul_add, add_mul, Finset.sum_add_distrib, aout, ain, p] at hscaled ⊢
  simp only [fieldDerivative] at hscaled ⊢
  ring_nf at hscaled ⊢
  have hcomm : (∑ j, fderiv ℝ
      (fun ζ => eval (C.Θ ζ ξ) (C.generatorTransferCoefficient i j)) η
        (wordBracket C.Xl (C.B j) η) * t.kernel ξ η) =
      ∑ j, t.kernel ξ η * fderiv ℝ
        (fun ζ => eval (C.Θ ζ ξ) (C.generatorTransferCoefficient i j)) η
          (wordBracket C.Xl (C.B j) η) := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hcomm]
  linarith

end RothschildStein.P1.LiftedChart
