-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.H2.CampanatoLimit
public import RothschildStein.H2.CampanatoCentres
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal
namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Geometric-series constant in BB Lemmas 7.40–7.42. -/
def campanatoTailConstant (P : DoublingPatch X) (α : ℝ) : ℝ :=
  (P.C_D + 1) / (1 - (1 / 2 : ℝ) ^ α)

/-- The geometric tail constant is positive for α > 0. -/
theorem campanatoTailConstant_pos (P : DoublingPatch X) {α : ℝ} (hα : 0 < α) :
    0 < campanatoTailConstant P α := by
  apply div_pos (by linarith [P.one_lt_C_D])
  exact sub_pos.mpr (Real.rpow_lt_one (by norm_num) (by norm_num) hα)

/-- Local Hölder estimate (7.29) with constant 4(c_C+C_D), BB Theorem 7.38, pp. 327 and 331. -/
theorem campanatoRepresentative_near (P : DoublingPatch X) {α : ℝ}
    (hα : 0 < α) (hα₁ : α ≤ 1) {u : X → ℝ} (hu : MemCampanato α P u)
    {x y : X} (hx : x ∈ P.S) (hy : y ∈ P.S) (hxy : dist x y ≤ 3 * P.ρ) :
    |campanatoRepresentative P α u x - campanatoRepresentative P α u y| ≤
      4 * (campanatoTailConstant P α + P.C_D) * (campanatoSeminorm α P u).toReal *
        dist x y ^ α := by
  by_cases he : x = y
  · subst y; simp [Real.zero_rpow hα.ne']
  have hr : 0 < dist x y := dist_pos.mpr he
  have hxB := campanatoRepresentative_approx P hα hu hx (show 0 < 2 * dist x y by positivity)
    (show 2 * dist x y ≤ 6 * P.ρ by linarith)
  have hyB := campanatoRepresentative_approx P hα hu hy (show 0 < 2 * dist x y by positivity)
    (show 2 * dist x y ≤ 6 * P.ρ by linarith)
  have hcB := campanatoConstant_centres P hu hx hy hr rfl (by linarith)
  have ht := abs_sub_le (campanatoRepresentative P α u x)
    (campanatoConstant P u x (2 * dist x y)) (campanatoRepresentative P α u y)
  have ht' := abs_sub_le (campanatoConstant P u x (2 * dist x y))
    (campanatoConstant P u y (2 * dist x y)) (campanatoRepresentative P α u y)
  rw [abs_sub_comm (campanatoConstant P u x _)] at hxB
  have htwo : (2 : ℝ) ^ α ≤ 2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hα₁
  have hpow : (2 * dist x y) ^ α ≤ 2 * dist x y ^ α := by
    rw [Real.mul_rpow (by norm_num) hr.le]
    exact mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hr.le α)
  have htail := (campanatoTailConstant_pos P hα).le
  have hcd : 0 ≤ P.C_D := by linarith [P.one_lt_C_D]
  have hp := mul_le_mul_of_nonneg_left hpow
    (mul_nonneg (add_nonneg htail hcd) (ENNReal.toReal_nonneg (a := campanatoSeminorm α P u)))
  change |campanatoConstant P u y _ - campanatoRepresentative P α u y| ≤
    campanatoTailConstant P α * _ * _ at hyB
  change |campanatoRepresentative P α u x - campanatoConstant P u x _| ≤
    campanatoTailConstant P α * _ * _ at hxB
  nlinarith
end RothschildStein.H2
