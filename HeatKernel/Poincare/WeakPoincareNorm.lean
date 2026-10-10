-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.SmoothWeakPoincare
public import HeatKernel.Poincare.PowerIntegralNorm

/-! Unnormalized seminorm form of the smooth weak horizontal Poincaré inequality. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory RothschildStein
open scoped ENNReal

namespace HeatKernel

/-- The smooth weak horizontal Poincaré inequality in Lp seminorm form, with the same
power-integral constant and exactly fourfold ball dilation. -/
theorem eLpNorm_weak_horizontalPoincare {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (x : Fin N → ℝ) {r p : ℝ} (hr : 0 < r) (hp : 1 ≤ p)
    (u : (Fin N → ℝ) → ℝ) (U : Set (Fin N → ℝ)) (hU : IsOpen U)
    (hsub : closure (horizontalBall (G.horizontalFields hq) x (4 * r)) ⊆ U)
    (hu : ContDiffOn ℝ 1 u U) :
    eLpNorm (fun y => u y - ⨍ z in horizontalBall (G.horizontalFields hq) x r, u z)
      (ENNReal.ofReal p) (volume.restrict (horizontalBall (G.horizontalFields hq) x r)) ≤
      ENNReal.ofReal (((2 : ℝ) ^ G.homogeneousDimension) ^ (1 / p) * (3 * r)) *
        eLpNorm (horizontalGradientNorm (G.horizontalFields hq) u) (ENNReal.ofReal p)
          (volume.restrict (horizontalBall (G.horizontalFields hq) x (4 * r))) := by
  let B := horizontalBall (G.horizontalFields hq) x r
  let B₄ := horizontalBall (G.horizontalFields hq) x (4 * r)
  let m := ⨍ z in B, u z
  let C := ((2 : ℝ) ^ G.homogeneousDimension) ^ (1 / p) * (3 * r)
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hB₄U : B₄ ⊆ U := subset_closure.trans hsub
  have hBB₄ : B ⊆ B₄ := by
    intro w hw'
    exact (show horizontalL2Distance (G.horizontalFields hq) x w < ENNReal.ofReal r from hw').trans_le
      (ENNReal.ofReal_le_ofReal (by linarith))
  have hf : AEStronglyMeasurable (fun y => u y - m) (volume.restrict B) :=
    ((hu.continuousOn.mono (hBB₄.trans hB₄U)).sub
      (continuousOn_const : ContinuousOn (fun _ : Fin N → ℝ => m) B)).aestronglyMeasurable
        (isOpen_horizontalBall G hq hqpos hspan x r).measurableSet
  have hg : AEStronglyMeasurable (horizontalGradientNorm (G.horizontalFields hq) u)
      (volume.restrict B₄) :=
    ((continuousOn_horizontalGradientNorm
      (fun i => (G.horizontalFields_contDiff hq i).continuous) hU hu).mono hB₄U).aestronglyMeasurable
        (isOpen_horizontalBall G hq hqpos hspan x (4 * r)).measurableSet
  have hC : 0 ≤ C := mul_nonneg (Real.rpow_nonneg (by positivity) _) (by linarith)
  have hCp : C ^ p = (2 : ℝ) ^ G.homogeneousDimension * (3 * r) ^ p := by
    dsimp only [C]
    rw [Real.mul_rpow (Real.rpow_nonneg (by positivity) _) (by linarith),
      one_div, Real.rpow_inv_rpow (by positivity) hp0.ne']
  apply eLpNorm_le_of_abs_rpow_integral_le hp0 hC hf hg
  have hh := lintegral_weak_horizontalPoincare G hq hqpos hspan hw x hr hp u U hU hsub hu
  rw [hCp, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
  norm_num only [ENNReal.ofReal_ofNat]
  simpa only [B, B₄, m, horizontalGradientNorm, abs_of_nonneg (Real.sqrt_nonneg _)] using hh

end HeatKernel
