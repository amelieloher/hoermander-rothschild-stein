-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.TypeZeroRemainderCutoff
public import RothschildStein.H3.CutoffKernelMeasurability
public import RothschildStein.H3.UnitSourceKernelSplit
public import RothschildStein.H2.IntegralDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter
namespace RothschildStein.H3

/-- On unit-supported inputs and unit-ball output points, the
fractional remainder integral is the exact nonsingular PV tail. -/
theorem typeZero_remainder_integral_eq_unitTail {N : ℕ}
    (G : HomogeneousGroup N) (ν : G2.HomogeneousNorm G)
    (h1 : ν.c = 1) (hsym : ν.Symmetric)
    (k F : (Fin N → ℝ) → ℝ)
    (hsu : ∀ y, 1 ≤ ν y → F y = 0) {x : Fin N → ℝ} (hx : ν x < 1) :
    H2.fractionalIntegral volume {y : Fin N → ℝ | ν y < 1}
      (fun a b => cutoffGroupKernel G (typeZeroRemainderCutoff ν) k a b) F x =
      G2.groupConvolution G F (typeZeroUnitTail ν k) x := by
  let K := fun a b => cutoffGroupKernel G (typeZeroRemainderCutoff ν) k a b
  have he (y : Fin N → ℝ) : K x y * F y = F y * typeZeroUnitTail ν k (G.mul (G.inv y) x) := by
    by_cases hy : ν y < 1
    · have ht := G2.gaugeDistance_triangle G ν x y 0
      rw [h1, one_mul, ← G2.gaugeDistance_symmetric G ν hsym 0 y] at ht
      simp only [G2.gaugeDistance, G2.inv_zero, G2.zero_mul] at ht
      have hρ : ν (G.mul (G.inv y) x) < 2 := by linarith
      have houter : radialKernelCutoffProfile 1 (ν (G.mul (G.inv y) x)) = 1 :=
        radialKernelCutoffProfile_eq_one (by norm_num) (by simpa using hρ.le)
      by_cases hnear : ν (G.mul (G.inv y) x) < 1
      · have hcut : typeZeroRemainderCutoff ν (G.mul (G.inv y) x) = 0 :=
          (typeZeroRemainderCutoff_properties G ν h1 hsym).2.2.2.1 _ hnear.le
        simp only [K, cutoffGroupKernel, hcut, zero_mul,
          typeZeroUnitTail_eq_zero_of_lt_one ν k hnear, mul_zero]
      · have hmem : G.mul (G.inv y) x ∈ {z | 1 ≤ ν z ∧ ν z ≤ 2} :=
          ⟨le_of_not_gt hnear, hρ.le⟩
        rw [typeZeroUnitTail, indicator_of_mem hmem]
        change (radialKernelCutoffProfile 1 (ν (G.mul (G.inv y) x)) *
          (1 - radialCutoff (ν (G.mul (G.inv y) x)))) * k (G.mul (G.inv y) x) * F y = _
        rw [houter]
        ring
    · rw [hsu y (le_of_not_gt hy), mul_zero, zero_mul]
  unfold H2.fractionalIntegral
  have hs : (∫ y in {y : Fin N → ℝ | ν y < 1}, K x y * F y) = ∫ y, K x y * F y := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    rw [hsu y (le_of_not_gt hy), mul_zero]
  rw [hs, G2.groupConvolution_eq_integral]
  exact integral_congr_ae (Eventually.of_forall he)

end RothschildStein.H3
