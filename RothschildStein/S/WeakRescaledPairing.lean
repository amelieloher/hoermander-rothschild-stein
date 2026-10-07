-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.RescaledKernelTest
public import RothschildStein.S.WeakDeriv

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Function Metric TopologicalSpace
open scoped Topology ContDiff
namespace RothschildStein.S
variable {n q : ℕ}

/-- Testing the weak singleton derivative with the
rescaled kernel gives its exact global pairing. Both integrands vanish
outside Ω, so no zero extension hypothesis is needed (BB p. 78). -/
theorem friedrichsKernelOp_weak_pairing
    (Ω : Opens (Fin n → ℝ)) (K : SmoothFriedrichsKernel n)
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)) (j : Fin q)
    {h g : (Fin n → ℝ) → ℝ} (hg : hasWeakWordDeriv X Ω [j] h g)
    {ε : ℝ} (hε : 0 < ε) (x : Fin n → ℝ) (hx : closedBall x ε ⊆ Ω) :
    friedrichsKernelOp K.family g ε x =
      ∫ z, h z * fieldTranspose (X j) (friedrichsRescaledKernel K.family ε x) z := by
  let φ := rescaledKernelTest Ω K hε x hx
  have hw := hg.2.2 φ
  change (∫ z in (Ω : Set (Fin n → ℝ)), g z * φ z) =
    ∫ z in (Ω : Set (Fin n → ℝ)), h z * fieldTranspose (X j) φ z at hw
  have hleft : (∫ z in (Ω : Set (Fin n → ℝ)), g z * φ z) = ∫ z, g z * φ z := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    have he : φ z = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hz (φ.tsupport_subset ht))
    simp only [he,mul_zero]
  have hright : (∫ z in (Ω : Set (Fin n → ℝ)), h z * fieldTranspose (X j) φ z) =
      ∫ z, h z * fieldTranspose (X j) φ z := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    have he : fieldTranspose (X j) φ z = 0 := image_eq_zero_of_notMem_tsupport
      (fun ht => hz (φ.tsupport_subset (tsupport_fieldTranspose_subset (X j) φ ht)))
    simp only [he,mul_zero]
  rw [hleft,hright] at hw
  rw [friedrichsKernelOp_eq_rescaled K.family g hε x]
  exact hw

end RothschildStein.S
