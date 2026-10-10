-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Geometry.BallVolume
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-! Rewriting point pairs in a horizontal ball as group translation increments. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory RothschildStein
open scoped ENNReal

namespace HeatKernel

/-- Two points in the same ball have a group increment in the doubled ball at the identity. -/
theorem preimage_horizontalBall_leftTranslation_subset {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) {x y : Fin N → ℝ} {r : ℝ}
    (hr : 0 ≤ r) (hy : y ∈ horizontalBall (G.horizontalFields hq) x r) :
    G.mul y ⁻¹' horizontalBall (G.horizontalFields hq) x r ⊆
      horizontalBall (G.horizontalFields hq) 0 (2 * r) := by
  intro z hz
  have ht := horizontalL2Distance_triangle (G.horizontalFields hq) y x (G.mul y z)
  have he : horizontalL2Distance (G.horizontalFields hq) y (G.mul y z) =
      horizontalL2Distance (G.horizontalFields hq) 0 z := by
    simpa only [G2.mul_zero] using horizontalL2Distance_leftTranslation G hq y 0 z
  rw [he, horizontalL2Distance_comm _ y x] at ht
  have hb := ENNReal.add_lt_add
    (show horizontalL2Distance (G.horizontalFields hq) x y < ENNReal.ofReal r from hy)
    (show horizontalL2Distance (G.horizontalFields hq) x (G.mul y z) < ENNReal.ofReal r from hz)
  change horizontalL2Distance (G.horizontalFields hq) 0 z < ENNReal.ofReal (2 * r)
  exact ht.trans_lt (hb.trans_eq (by rw [← ENNReal.ofReal_add hr hr]; congr 1; ring))

/-- Haar invariance bounds the integral over a point pair by the integral over all
increments in the doubled horizontal ball. -/
theorem lintegral_pair_le_lintegral_translation {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    {x y : Fin N → ℝ} {r : ℝ} (hr : 0 ≤ r)
    (hy : y ∈ horizontalBall (G.horizontalFields hq) x r)
    {F : (Fin N → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ z in horizontalBall (G.horizontalFields hq) x r, F z) ≤
      ∫⁻ z in horizontalBall (G.horizontalFields hq) 0 (2 * r), F (G.mul y z) := by
  rw [← (G2.measurePreserving_leftTranslation G y).setLIntegral_comp_preimage
    (isOpen_horizontalBall G hq hqpos hspan x r).measurableSet hF]
  exact lintegral_mono_set (preimage_horizontalBall_leftTranslation_subset G hq hr hy)

end HeatKernel
