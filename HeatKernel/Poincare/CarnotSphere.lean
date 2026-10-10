-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Geometry.CarnotPoint
public import HeatKernel.Geometry.GroupCovariance
public import Mathlib.Tactic.FieldSimp

/-! Nonempty spheres for homogeneous horizontal metrics. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set RothschildStein
open scoped ENNReal

namespace HeatKernel.CarnotPoint

/-- Homogeneous dilation produces a point at every positive prescribed distance from
any center when there is at least one horizontal generator. -/
theorem exists_dist_eq {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N)
    (hqpos : 0 < q) (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (x : CarnotPoint G hq hqpos hspan) {r : ℝ} (hr : 0 < r) :
    ∃ y : CarnotPoint G hq hqpos hspan, dist x y = r := by
  let o : CarnotPoint G hq hqpos hspan := fun _ => 0
  let x₀ : Fin N → ℝ := x
  have hN : 0 < N := hqpos.trans_le hq
  let z : CarnotPoint G hq hqpos hspan := fun _ => 1
  let z₀ : Fin N → ℝ := z
  have hz : z ≠ o := by
    intro he
    have hh := congrFun he ⟨0, hN⟩
    change (1 : ℝ) = 0 at hh
    norm_num at hh
  have hD : 0 < dist o z := dist_pos.mpr hz.symm
  let c := r / dist o z
  have hc : 0 < c := div_pos hr hD
  let y₀ := G.mul x₀ (G.dilate c z₀)
  let y : CarnotPoint G hq hqpos hspan := y₀
  refine ⟨y, ?_⟩
  have ht := horizontalL2Distance_leftTranslation G hq x₀ (0 : Fin N → ℝ) (G.dilate c z₀)
  simp only [G2.mul_zero] at ht
  have hd := horizontalL2Distance_dilate G hq hw hc (0 : Fin N → ℝ) z₀
  simp only [G2.dilate_zero] at hd
  have he : (horizontalL2Distance (G.horizontalFields hq) 0 z₀).toReal =
      dist o z := by
    rw [dist_edist o z]
    rfl
  change (horizontalL2Distance (G.horizontalFields hq) x₀ y₀).toReal = r
  dsimp only [y₀]
  rw [ht, hd, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hc.le, he]
  exact div_mul_cancel₀ r hD.ne'

end HeatKernel.CarnotPoint
