-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.SmoothPoincarePower
public import HeatKernel.Poincare.PowerIntegralNorm

/-! Same-ball horizontal Poincaré estimates in finite-exponent seminorms. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory RothschildStein
open scoped ENNReal

namespace HeatKernel

/-- Interior C¹ regularity and L¹ integrability suffice for a uniform same-ball
seminorm estimate, including when the gradient seminorm is infinite. -/
theorem exists_uniform_horizontalPoincare_seminorm_constant {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {κ p : ℝ} (hκ : 240 < κ) (k : ℕ) (hk : 0 < k)
    (hscale : 2 * κ + 22 ≤ (k : ℝ)) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : Fin N → ℝ) (r : ℝ), 0 < r →
      ∀ u : (Fin N → ℝ) → ℝ,
        ContDiffOn ℝ 1 u (horizontalBall (G.horizontalFields hq) x r) →
        IntegrableOn u (horizontalBall (G.horizontalFields hq) x r) →
        eLpNorm (fun y => u y - ⨍ z in horizontalBall (G.horizontalFields hq) x r, u z)
          (ENNReal.ofReal p) (volume.restrict (horizontalBall (G.horizontalFields hq) x r)) ≤
          ENNReal.ofReal (C * r) *
            eLpNorm (horizontalGradientNorm (G.horizontalFields hq) u) (ENNReal.ofReal p)
              (volume.restrict (horizontalBall (G.horizontalFields hq) x r)) := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_horizontalPoincare_power_constant
    G hq hqpos hspan hw hκ k hk hscale hp
  refine ⟨C, hC, ?_⟩
  intro x r hr u hu hf
  have hB := isOpen_horizontalBall G hq hqpos hspan x r
  have hfosc : AEStronglyMeasurable
      (fun y => u y - ⨍ z in horizontalBall (G.horizontalFields hq) x r, u z)
      (volume.restrict (horizontalBall (G.horizontalFields hq) x r)) :=
    (hu.continuousOn.sub continuousOn_const).aestronglyMeasurable hB.measurableSet
  have hg : AEStronglyMeasurable (horizontalGradientNorm (G.horizontalFields hq) u)
      (volume.restrict (horizontalBall (G.horizontalFields hq) x r)) :=
    (continuousOn_horizontalGradientNorm
    (fun i => (G.horizontalFields_contDiff hq i).continuous) hB hu).aestronglyMeasurable hB.measurableSet
  apply eLpNorm_le_of_abs_rpow_integral_le (lt_of_lt_of_le zero_lt_one hp)
    (mul_nonneg hC.le hr.le) hfosc hg
  have hgn : ∀ y, 0 ≤ horizontalGradientNorm (G.horizontalFields hq) u y :=
    fun _ => Real.sqrt_nonneg _
  simpa only [abs_of_nonneg (hgn _)] using
    hbound (show CarnotPoint G hq hqpos hspan from x) r hr u hu hf

end HeatKernel
