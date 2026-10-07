-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.KernelWeightNormalization
public import RothschildStein.H2.KernelClass

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Metric MeasureTheory
namespace RothschildStein.H3

/-- A singular kernel vanishing through distance one is a
fractional kernel of order one. The smoothness coefficient doubles. -/
theorem kernelClass_fractional_of_unit_diagonal_gap {N : ℕ}
    (G : HomogeneousGroup N) (ν : G2.HomogeneousNorm G)
    (h1 : ν.c = 1) (hsym : ν.Symmetric) {A S : ℝ}
    {K : ControlCarrier N → ControlCarrier N → ℝ}
    (H : let _metric := gaugeMetric G ν h1 hsym
      H2.KernelClass volume univ 1 0 A S K)
    (hgap : let _metric := gaugeMetric G ν h1 hsym
      ∀ x y : ControlCarrier N, dist x y ≤ 1 → K x y = 0) :
    let _metric := gaugeMetric G ν h1 hsym
    H2.KernelClass volume univ 1 1 A (2 * S) K := by
  let _metric : MetricSpace (ControlCarrier N) := gaugeMetric G ν h1 hsym
  let m := (volume {z : Fin N → ℝ | ν z < 1}).toReal
  have hm : 0 < m := gauge_unit_volume_toReal_pos G ν
  have hweight (x y : ControlCarrier N) (hxy : x ≠ y) :
      H2.kernelWeight (volume : Measure (ControlCarrier N)) 0 x y =
        dist x y ^ (-(G.homogeneousDimension : ℝ)) / m ∧
      H2.kernelWeight (volume : Measure (ControlCarrier N)) 1 x y =
        dist x y ^ (1 - (G.homogeneousDimension : ℝ)) / m := by
    constructor
    · have hz : H2.kernelWeight (volume : Measure (ControlCarrier N)) 0 x y =
          dist x y ^ ((0 : ℝ) - (G.homogeneousDimension : ℝ)) / m :=
        kernelWeight_gauge_eq G ν h1 hsym 0 x y hxy
      rw [zero_sub] at hz
      exact hz
    · exact kernelWeight_gauge_eq G ν h1 hsym 1 x y hxy
  refine ⟨H.measurable_E, H.measurable, H.β_pos, H.β_le_one, by norm_num,
    H.A_nonneg, mul_nonneg (by norm_num) H.S_nonneg, ?_, ?_⟩
  · intro x hx y hy hxy
    by_cases hnear : dist x y ≤ 1
    · rw [hgap x y hnear, abs_zero]
      exact mul_nonneg H.A_nonneg (H2.kernelWeight_nonneg volume 1 x y)
    · have hp : dist x y ^ (-(G.homogeneousDimension : ℝ)) ≤
          dist x y ^ (1 - (G.homogeneousDimension : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (lt_of_not_ge hnear).le (by linarith)
      have hw := div_le_div_of_nonneg_right hp hm.le
      rw [← (hweight x y hxy).1, ← (hweight x y hxy).2] at hw
      exact (H.size x hx y hy hxy).trans (mul_le_mul_of_nonneg_left hw H.A_nonneg)
  · intro x₀ hx₀ x hx y hy hsep
    have hρ : 0 < dist x₀ y := by linarith [dist_nonneg (x := x₀) (y := x)]
    have hxy : x₀ ≠ y := dist_pos.mp hρ
    by_cases hnear : dist x₀ y ≤ 1 / 2
    · have hx₀y : dist x₀ y ≤ 1 := by linarith
      have hxy' : dist x y ≤ 1 := by
        have ht := dist_triangle x x₀ y
        rw [dist_comm x x₀] at ht
        linarith
      rw [hgap x₀ y hx₀y, hgap x y hxy', sub_self, abs_zero]
      exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) H.S_nonneg)
        (H2.kernelWeight_nonneg volume 1 x₀ y))
        (Real.rpow_nonneg (div_nonneg (dist_nonneg (x := x₀) (y := x)) hρ.le) 1)
    · have he : dist x₀ y ^ (-(G.homogeneousDimension : ℝ)) =
          dist x₀ y ^ (1 - (G.homogeneousDimension : ℝ)) / dist x₀ y := by
        rw [← Real.rpow_sub_one hρ.ne']
        congr 1
        ring
      have hp : dist x₀ y ^ (-(G.homogeneousDimension : ℝ)) ≤
          2 * dist x₀ y ^ (1 - (G.homogeneousDimension : ℝ)) := by
        rw [he]
        apply (div_le_iff₀ hρ).mpr
        have hc : 1 ≤ 2 * dist x₀ y := by linarith [lt_of_not_ge hnear]
        have hb := mul_le_mul_of_nonneg_left hc
          (Real.rpow_nonneg hρ.le (1 - (G.homogeneousDimension : ℝ)))
        nlinarith
      have hw : H2.kernelWeight (volume : Measure (ControlCarrier N)) 0 x₀ y ≤
          2 * H2.kernelWeight (volume : Measure (ControlCarrier N)) 1 x₀ y := by
        rw [(hweight x₀ y hxy).1, (hweight x₀ y hxy).2]
        exact (div_le_div_of_nonneg_right hp hm.le).trans_eq (by ring)
      have hb := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hw H.S_nonneg)
        (Real.rpow_nonneg (div_nonneg (dist_nonneg (x := x₀) (y := x)) hρ.le) 1)
      exact (H.smooth x₀ hx₀ x hx y hy hsep).trans (hb.trans_eq (by ring))

end RothschildStein.H3
