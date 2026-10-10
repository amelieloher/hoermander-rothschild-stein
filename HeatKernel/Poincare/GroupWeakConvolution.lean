-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.GroupConvolutionDerivative
public import HeatKernel.Poincare.GroupKernelTest
public import RothschildStein.S.MollifierZeroExtension

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal
namespace HeatKernel

/-- Group convolution commutes with a weak invariant derivative at every point where
the translated kernel support stays in the weak derivative domain. -/
theorem fieldDerivative_groupConvolution_zeroExtension_of_support
    {N : ℕ} (G : HomogeneousGroup N) (v x : Fin N → ℝ)
    (Ω : Opens (Fin N → ℝ)) {f g η : (Fin N → ℝ) → ℝ}
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hf : MemLp f p (volume.restrict (Ω : Set (Fin N → ℝ))))
    (hw : hasWeakWordDeriv (fun _ : Fin 1 => G2.leftField G v) Ω [0] f g)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hc : HasCompactSupport η)
    (hs : tsupport (fun z => η (G.mul x (G.inv z))) ⊆ Ω) :
    fieldDerivative (G2.leftField G v)
      (G2.groupConvolution G η ((Ω : Set (Fin N → ℝ)).indicator f)) x =
      G2.groupConvolution G η ((Ω : Set (Fin N → ℝ)).indicator g) x := by
  let D := fun z => fieldDerivative (G2.leftField G v)
    (fun y => η (G.mul y (G.inv z))) x
  have hIF : (∫ z, (Ω : Set (Fin N → ℝ)).indicator f z * D z) =
      ∫ z in (Ω : Set (Fin N → ℝ)), f z * D z := by
    rw [← integral_indicator Ω.isOpen.measurableSet]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun z => by
      by_cases hz : z ∈ (Ω : Set (Fin N → ℝ)) <;> simp [hz])
  have hIG : G2.groupConvolution G η ((Ω : Set (Fin N → ℝ)).indicator g) x =
      ∫ z in (Ω : Set (Fin N → ℝ)), g z * η (G.mul x (G.inv z)) := by
    rw [G2.groupConvolution_def, ← integral_indicator Ω.isOpen.measurableSet]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun z => by
      by_cases hz : z ∈ (Ω : Set (Fin N → ℝ)) <;> simp [hz, mul_comm])
  rw [fieldDerivative_groupConvolution_kernel G hη hc
    (((S.memLp_zeroExtension_iff Ω.isOpen.measurableSet f).mpr hf).locallyIntegrable hp)]
  exact hIF.trans ((integral_group_kernel_weak_derivative_of_support G v x Ω
    hw hη hc hs).symm.trans hIG.symm)

end HeatKernel
