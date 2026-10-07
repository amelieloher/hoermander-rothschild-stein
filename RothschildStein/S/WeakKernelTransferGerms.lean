-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.WeakRescaledPairing
public import RothschildStein.S.RescaledKernelDifferentiation
public import RothschildStein.S.RescaledTransferIdentity
public import RothschildStein.S.CompactKernelDirectionalTest
public import RothschildStein.S.FieldGermExtension

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Function Metric TopologicalSpace
open scoped Topology ContDiff
namespace RothschildStein.S
variable {n q : ℕ}

/-- Weak transfer after replacing a local coefficient field by
any globally smooth field with matching germs on the common support.
The weak predicate retains the original field (BB pp. 78–79; local
coefficient). -/
theorem weak_friedrichsKernel_transfer_of_coefficient_germs
    (Ω : Opens (Fin n → ℝ)) (K : SmoothFriedrichsKernel n)
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)) (j : Fin q)
    (B : (Fin n → ℝ) → (Fin n → ℝ)) (hB : ContDiff ℝ (⊤ : ℕ∞) B)
    {h g : (Fin n → ℝ) → ℝ} (hg : hasWeakWordDeriv X Ω [j] h g)
    {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r) (x : Fin n → ℝ)
    (hx : closedBall x (ε+r) ⊆ Ω)
    (hG : ∀ z ∈ closedBall x (ε+r), B =ᶠ[𝓝 z] X j) :
    fieldDerivative (X j) (friedrichsKernelOp K.family h ε) x =
      friedrichsKernelOp K.family g ε x +
        friedrichsKernelOp (smoothKernelTransfer K B hB).family h ε x := by
  have hsmall : closedBall x ε ⊆ Ω :=
    (closedBall_subset_closedBall (by linarith)).trans hx
  let φ := rescaledKernelTest Ω K hε x hsmall
  let C : Compacts (Fin n → ℝ) := ⟨closedBall x (ε+r),isCompact_closedBall x (ε+r)⟩
  have hk := contDiff_friedrichsRescaledKernel K ε
  have hks : ∀ a z, a ∈ ball x r → z ∉ C →
      friedrichsRescaledKernel K.family ε a z = 0 :=
    fun a z ha hz => friedrichsRescaledKernel_eq_zero_of_notMem_common_ball K hε x a z ha hz
  let ψ := compactKernelDirectionalTest Ω C hx hk x (B x) hr hks
  have hiD : Integrable (fun z => h z *
      fderiv ℝ (uncurry (friedrichsRescaledKernel K.family ε)) (x,z) (B x,0)) volume :=
    integrable_mul_test Ω hg.1 ψ
  have hiT : Integrable (fun z => h z *
      fieldTranspose B (friedrichsRescaledKernel K.family ε x) z) volume := by
    have ht := integrable_mul_test Ω hg.1 (fieldTransposeTest Ω B hB.contDiffOn φ)
    have hφ : (φ : (Fin n → ℝ) → ℝ) = friedrichsRescaledKernel K.family ε x := rfl
    simpa only [fieldTransposeTest_coe,hφ] using! ht
  have ht : fieldTranspose B (friedrichsRescaledKernel K.family ε x) =
      fieldTranspose (X j) (friedrichsRescaledKernel K.family ε x) :=
    fieldTranspose_eq_of_coefficient_germs C B (X j) hG _
      ((tsupport_friedrichsRescaledKernel_subset K hε x).trans
        (closedBall_subset_closedBall (by linarith)))
  have hp := friedrichsKernelOp_weak_pairing Ω K X j hg hε x hsmall
  rw [← ht] at hp
  have he : fieldDerivative B (friedrichsKernelOp K.family h ε) x -
      friedrichsKernelOp K.family g ε x =
      friedrichsKernelOp (smoothKernelTransfer K B hB).family h ε x := by
    unfold fieldDerivative
    rw [fderiv_friedrichsKernelOp_apply_of_interior_ball Ω K hg.1 hε hr x (B x) hx,
      hp,
      ← integral_sub hiD hiT,
      friedrichsKernelOp_eq_rescaled (smoothKernelTransfer K B hB).family h hε x]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro z
    change h z * fderiv ℝ (uncurry (friedrichsRescaledKernel K.family ε)) (x,z) (B x,0) -
      h z * fieldTranspose B (friedrichsRescaledKernel K.family ε x) z = _
    rw [← mul_sub,← fderiv_productSection_first_apply hk x z (B x)]
    exact congrArg (fun a => h z * a) (rescaledKernel_transfer_identity K B hB hε.ne' x z)
  have hc : B x = X j x := (hG x (by simp [mem_closedBall]; positivity)).eq_of_nhds
  unfold fieldDerivative at he ⊢
  rw [← hc]
  linarith

end RothschildStein.S
