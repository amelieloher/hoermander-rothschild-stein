-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.WeakPoincareIntegral
public import HeatKernel.Poincare.LocalIntegrability

/-! Weak Poincaré inequality for functions continuously differentiable near a closed ball. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory RothschildStein
open scoped ENNReal

namespace HeatKernel

/-- Weak horizontal Poincaré with dilation four and exact integral factor
2^Q(3r)^p, for every real exponent p≥1 under local continuous differentiability. -/
theorem lintegral_weak_horizontalPoincare {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (x : Fin N → ℝ) {r p : ℝ} (hr : 0 < r) (hp : 1 ≤ p)
    (u : (Fin N → ℝ) → ℝ) (U : Set (Fin N → ℝ)) (hU : IsOpen U)
    (hsub : closure (horizontalBall (G.horizontalFields hq) x (4 * r)) ⊆ U)
    (hu : ContDiffOn ℝ 1 u U) :
    (∫⁻ y in horizontalBall (G.horizontalFields hq) x r,
      ENNReal.ofReal (|u y - ⨍ z in horizontalBall (G.horizontalFields hq) x r, u z| ^ p)) ≤
      (2 : ℝ≥0∞) ^ G.homogeneousDimension * ENNReal.ofReal ((3 * r) ^ p) *
        ∫⁻ w in horizontalBall (G.horizontalFields hq) x (4 * r),
          ENNReal.ofReal ((horizontalGradientNorm (G.horizontalFields hq) u w) ^ p) := by
  classical
  let B := horizontalBall (G.horizontalFields hq) x r
  let B₄ := horizontalBall (G.horizontalFields hq) x (4 * r)
  let v := U.indicator u
  let g := fun w => (horizontalGradientNorm (G.horizontalFields hq) u w) ^ p
  let F := fun w => ENNReal.ofReal (U.indicator g w)
  have hB₄U : B₄ ⊆ U := subset_closure.trans hsub
  have hBB₄ : B ⊆ B₄ := by
    intro w hw'
    exact (show horizontalL2Distance (G.horizontalFields hq) x w < ENNReal.ofReal r from hw').trans_le
      (ENNReal.ofReal_le_ofReal (by linarith))
  have hBU : B ⊆ U := hBB₄.trans hB₄U
  have hv : ContDiffOn ℝ 1 v U :=
    fun w hw' => (contDiffAt_indicator_of_isOpen hU hw' hu).contDiffWithinAt
  have hvmeas : Measurable v := measurable_indicator_of_continuousOn hU hu.continuousOn
  have hv₄ : ∀ w ∈ B₄, ContDiffAt ℝ 1 v w :=
    fun w hw' => contDiffAt_indicator_of_isOpen hU (hB₄U hw') hu
  have hgc : ContinuousOn g U :=
    (Real.continuous_rpow_const (le_trans zero_le_one hp)).comp_continuousOn
      (continuousOn_horizontalGradientNorm (fun i => (G.horizontalFields_contDiff hq i).continuous) hU hu)
  have hF : Measurable F := ENNReal.continuous_ofReal.measurable.comp
    (measurable_indicator_of_continuousOn hU hgc)
  have henergy : ∀ w ∈ B₄, F w =
      ENNReal.ofReal ((horizontalGradientNorm (G.horizontalFields hq) v w) ^ p) := by
    intro w hw'
    have he := fderiv_indicator_of_isOpen hU (f := u) (hB₄U hw')
    simp only [F, indicator_of_mem (hB₄U hw'), g, horizontalGradientNorm, v, he]
  obtain ⟨hvi, hpairs⟩ := integrableOn_and_pairwise_rpow_of_contDiffOn G hq hqpos hspan hw x hr.le hp
    ((closure_mono hBB₄).trans hsub) hv
  have hh := lintegral_weak_horizontalPoincare_of_integrable G hq hqpos hspan hw x hr hp
    v hvmeas hv₄ hvi hpairs F hF henergy
  have hBmeas := (isOpen_horizontalBall G hq hqpos hspan x r).measurableSet
  have hB₄meas := (isOpen_horizontalBall G hq hqpos hspan x (4 * r)).measurableSet
  have hmean : (⨍ w in B, v w) = ⨍ w in B, u w :=
    setAverage_congr_fun hBmeas (Filter.Eventually.of_forall fun w hw' => indicator_of_mem (hBU hw') u)
  have hleft : (∫⁻ y in B, ENNReal.ofReal (|v y - ⨍ z in B, v z| ^ p)) =
      ∫⁻ y in B, ENNReal.ofReal (|u y - ⨍ z in B, u z| ^ p) := by
    apply setLIntegral_congr_fun hBmeas
    intro y hy
    simp only [hmean, v, indicator_of_mem (hBU hy)]
  have hright : (∫⁻ w in B₄, F w) = ∫⁻ w in B₄, ENNReal.ofReal (g w) := by
    apply setLIntegral_congr_fun hB₄meas
    intro w hw'
    simp only [F, indicator_of_mem (hB₄U hw')]
  rw [hleft, hright] at hh
  exact hh

end HeatKernel
