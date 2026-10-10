-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.GroupKernelDerivative
public import RothschildStein.G2.InvariantDivergence
public import RothschildStein.S.WeakDeriv

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
namespace HeatKernel

/-- Testing a weak invariant derivative against a translated group kernel moves its
field derivative to the parameter variable. The supported test is supplied explicitly. -/
theorem integral_group_kernel_weak_derivative_of_test
    {N : ℕ} (G : HomogeneousGroup N) (v x : Fin N → ℝ)
    (Ω : Opens (Fin N → ℝ)) {f g η : (Fin N → ℝ) → ℝ}
    (hw : hasWeakWordDeriv (fun _ : Fin 1 => G2.leftField G v) Ω [0] f g)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (φ : TestFunction Ω ℝ (⊤ : ℕ∞))
    (hφ : (φ : (Fin N → ℝ) → ℝ) = fun z => η (G.mul x (G.inv z))) :
    (∫ z in (Ω : Set (Fin N → ℝ)), g z * η (G.mul x (G.inv z))) =
      ∫ z in (Ω : Set (Fin N → ℝ)), f z *
        fieldDerivative (G2.leftField G v) (fun y => η (G.mul y (G.inv z))) x := by
  have ht (z : Fin N → ℝ) :
      wordTranspose (fun _ : Fin 1 => G2.leftField G v) [0] φ z =
        fieldDerivative (G2.leftField G v) (fun y => η (G.mul y (G.inv z))) x := by
    simp only [wordTranspose, G2.leftField_transpose G v φ φ.contDiff]
    rw [hφ]
    exact (fieldDerivative_group_kernel_swap G v x z (hη.of_le (by simp))).symm
  calc
    _ = ∫ z in (Ω : Set (Fin N → ℝ)), g z * φ z := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun z => by rw [hφ])
    _ = ∫ z in (Ω : Set (Fin N → ℝ)), f z *
        wordTranspose (fun _ : Fin 1 => G2.leftField G v) [0] φ z := hw.2.2 φ
    _ = _ := by simp_rw [ht]

end HeatKernel
