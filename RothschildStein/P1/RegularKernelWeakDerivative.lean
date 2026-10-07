-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.CompactKernelDerivative
public import RothschildStein.P1.RegularKernelFiberDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.P1
variable {N : ℕ} {F : KernelFrame N}

/-- The actual action of a regular kernel on an interior test
has weak output derivative equal to the action of its differentiated kernel. -/
theorem regularKernel_action_hasWeakFieldDeriv
    {r : (Fin N → ℝ) → (Fin N → ℝ) → ℝ}
    (hr : IsRegularKernel F 1 r)
    (X : Fin 1 → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (F.V : Set (Fin N → ℝ)))
    (ψ : TestFunction F.V ℝ (⊤ : ℕ∞)) :
    hasWeakWordDeriv X F.V [0] (fun ξ => ∫ η, r ξ η * ψ η)
      (fun ξ => ∫ η, fieldDerivative (X 0) (fun x => r x η) ξ * ψ η) := by
  let Φ := fun q : (Fin N → ℝ) × (Fin N → ℝ) => r q.1 q.2 * ψ q.2
  have hΦ : ContDiff ℝ 1 Φ := hr.1.mul ((ψ.contDiff.of_le (by simp)).comp contDiff_snd)
  have hd : ∀ ξ η, fieldDerivative (X 0) (fun x => Φ (x, η)) ξ =
      fieldDerivative (X 0) (fun x => r x η) ξ * ψ η := by
    intro ξ η
    have hrη : DifferentiableAt ℝ (fun x => r x η) ξ :=
      (hr.1.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) ξ
    dsimp [Φ, fieldDerivative]
    rw [fderiv_mul_const hrη]
    simp [mul_comm]
  have he : (fun ξ => ∫ η in tsupport (ψ : (Fin N → ℝ) → ℝ), Φ (ξ, η)) =
      (fun ξ => ∫ η, r ξ η * ψ η) := by
    funext ξ
    exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun η hη => by
      dsimp [Φ]
      rw [image_eq_zero_of_notMem_tsupport hη, mul_zero])
  have heD : (fun ξ => ∫ η in tsupport (ψ : (Fin N → ℝ) → ℝ),
      fieldDerivative (X 0) (fun x => Φ (x, η)) ξ) =
      (fun ξ => ∫ η, fieldDerivative (X 0) (fun x => r x η) ξ * ψ η) := by
    funext ξ
    simp_rw [hd]
    exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun η hη => by
      rw [image_eq_zero_of_notMem_tsupport hη, mul_zero])
  have hw := compactKernelIntegral_hasWeakFieldDeriv F.V X hX Φ hΦ
    (tsupport (ψ : (Fin N → ℝ) → ℝ)) ψ.hasCompactSupport.isCompact
  rw [he, heD] at hw
  exact hw

end RothschildStein.P1
