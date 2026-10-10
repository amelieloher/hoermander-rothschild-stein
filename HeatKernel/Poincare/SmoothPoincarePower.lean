-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.CarnotMeanEnergy
public import HeatKernel.Poincare.WhitneyCoefficient

/-! Uniform same-ball Poincaré power bounds for interior smooth functions. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory RothschildStein
open scoped ENNReal

namespace HeatKernel

/-- The same-ball power inequality has a positive constant chosen before the center,
radius, and function. Only interior C¹ regularity and L¹ integrability are required. -/
theorem exists_uniform_horizontalPoincare_power_constant {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {κ p : ℝ} (hκ : 240 < κ) (k : ℕ) (hk : 0 < k)
    (hscale : 2 * κ + 22 ≤ (k : ℝ)) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : CarnotPoint G hq hqpos hspan) (r : ℝ), 0 < r →
      ∀ u : (Fin N → ℝ) → ℝ,
        ContDiffOn ℝ 1 u (horizontalBall (G.horizontalFields hq) x r) →
        IntegrableOn u (horizontalBall (G.horizontalFields hq) x r) →
        (∫⁻ y in horizontalBall (G.horizontalFields hq) x r,
          ENNReal.ofReal (|u y - ⨍ z in horizontalBall (G.horizontalFields hq) x r, u z| ^ p)) ≤
          ENNReal.ofReal ((C * r) ^ p) *
            ∫⁻ y in horizontalBall (G.horizontalFields hq) x r,
              ENNReal.ofReal (horizontalGradientNorm (G.horizontalFields hq) u y ^ p) := by
  obtain ⟨C, hC, hcoef⟩ := exists_positive_whitney_coefficient G.homogeneousDimension
    (by linarith : 0 < κ) (lt_of_lt_of_le zero_lt_one hp) k hk
  refine ⟨C, hC, ?_⟩
  intro x r hr u hu hf
  have hh := lintegral_mean_oscillation_le_horizontal_energy G hq hqpos hspan hw
    x hr hκ k hk hscale hp u hu hf
  rw [hcoef r hr] at hh
  exact hh

end HeatKernel
