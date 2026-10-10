-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.GroupWeakKernelIdentity

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
namespace HeatKernel

/-- A compact smooth group kernel becomes a test function whenever its translated
support lies inside the open domain. -/
theorem exists_group_kernel_test {N : ℕ} (G : HomogeneousGroup N)
    (x : Fin N → ℝ) (Ω : Opens (Fin N → ℝ)) {η : (Fin N → ℝ) → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hc : HasCompactSupport η)
    (hs : tsupport (fun z => η (G.mul x (G.inv z))) ⊆ Ω) :
    ∃ φ : TestFunction Ω ℝ (⊤ : ℕ∞),
      (φ : (Fin N → ℝ) → ℝ) = fun z => η (G.mul x (G.inv z)) := by
  let e : (Fin N → ℝ) ≃ₜ (Fin N → ℝ) :=
    { toFun := fun z => G.mul x (G.inv z)
      invFun := fun w => G.mul (G.inv w) x
      left_inv := fun z => by
        simp only [G2.inv_product, G2.inv_inv, G2.mul_assoc, G2.inv_mul, G2.mul_zero]
      right_inv := fun w => by
        simp only [G2.inv_product, G2.inv_inv, ← G2.mul_assoc, G2.mul_inv, G2.zero_mul]
      continuous_toFun := (G2.contDiff_leftTranslation G x).continuous.comp
        (G2.contDiff_inv G).continuous
      continuous_invFun := (G2.contDiff_rightTranslation G x).continuous.comp
        (G2.contDiff_inv G).continuous }
  refine ⟨⟨fun z => η (G.mul x (G.inv z)),
    hη.comp ((G2.contDiff_leftTranslation G x).comp (G2.contDiff_inv G)),
    ?_, hs⟩, rfl⟩
  exact hc.comp_homeomorph e

/-- The interior support condition suffices to test a weak invariant derivative against
an actual translated compact smooth kernel. -/
theorem integral_group_kernel_weak_derivative_of_support
    {N : ℕ} (G : HomogeneousGroup N) (v x : Fin N → ℝ)
    (Ω : Opens (Fin N → ℝ)) {f g η : (Fin N → ℝ) → ℝ}
    (hw : hasWeakWordDeriv (fun _ : Fin 1 => G2.leftField G v) Ω [0] f g)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hc : HasCompactSupport η)
    (hs : tsupport (fun z => η (G.mul x (G.inv z))) ⊆ Ω) :
    (∫ z in (Ω : Set (Fin N → ℝ)), g z * η (G.mul x (G.inv z))) =
      ∫ z in (Ω : Set (Fin N → ℝ)), f z *
        fieldDerivative (G2.leftField G v) (fun y => η (G.mul y (G.inv z))) x := by
  obtain ⟨φ, hφ⟩ := exists_group_kernel_test G x Ω hη hc hs
  exact integral_group_kernel_weak_derivative_of_test G v x Ω hw hη φ hφ

end HeatKernel
