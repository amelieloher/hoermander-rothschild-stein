-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Geometry.HorizontalMetric

public import HeatKernel.Geometry.HorizontalSubarc
public import HeatKernel.Geometry.GroupCovariance
public import HeatKernel.Geometry.BallCovariance

/-! Horizontal paths translated from the identity and their containing balls. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory RothschildStein
open scoped ENNReal

namespace HeatKernel

/-- Left translation preserves horizontal curves and their controls. -/
theorem IsHorizontalCurveOn.leftTranslation {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q ≤ N) {γ : ℝ → (Fin N → ℝ)} {a : Fin q → ℝ → ℝ} {s t : ℝ}
    (h : IsHorizontalCurveOn (G.horizontalFields hq) γ a s t) (y : Fin N → ℝ) :
    IsHorizontalCurveOn (G.horizontalFields hq) (fun r => G.mul y (γ r)) a s t := by
  have hh := h.map ((G2.contDiff_leftTranslation G y).of_le (by simp))
    (by norm_num : (0 : ℝ) < 1) (Y := G.horizontalFields hq)
    (fun i z => by
      simpa only [one_smul, HomogeneousGroup.horizontalFields,
        G2.canonicalField_eq_leftField] using
        G2.leftField_invariant G (Hormander.Interface.basisVec (Fin.castLE hq i)) y z)
  simpa only [Function.comp_def, one_mul] using hh

/-- A unit-speed path of length less than three radii, translated from a point in a ball,
stays in the concentric ball with four times the radius. -/
theorem translated_horizontalCurve_image_subset_four_ball {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) {γ : ℝ → (Fin N → ℝ)}
    {a : Fin q → ℝ → ℝ} {ℓ r : ℝ} {x y : Fin N → ℝ}
    (h : IsHorizontalCurveOn (G.horizontalFields hq) γ a 0 ℓ)
    (hℓ : 0 ≤ ℓ) (hr : 0 < r) (hlength : ℓ < 3 * r) (hzero : γ 0 = 0)
    (ha : ∀ u, controlNorm a u ≤ 1)
    (hy : y ∈ horizontalBall (G.horizontalFields hq) x r) :
    (fun t => G.mul y (γ t)) '' uIcc 0 ℓ ⊆
      horizontalBall (G.horizontalFields hq) x (4 * r) := by
  rintro z ⟨t, ht, rfl⟩
  rw [uIcc_of_le hℓ] at ht
  have hd := h.subarc_distance_le_of_controlNorm_le_one (le_refl 0) ht.1 ht.2
    (fun u _ => ha u)
  rw [hzero, sub_zero] at hd
  have hd' : horizontalL2Distance (G.horizontalFields hq) 0 (γ t) < ENNReal.ofReal (3 * r) :=
    hd.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (ht.2.trans_lt hlength))
  have he : horizontalL2Distance (G.horizontalFields hq) y (G.mul y (γ t)) =
      horizontalL2Distance (G.horizontalFields hq) 0 (γ t) := by
    simpa only [G2.mul_zero] using horizontalL2Distance_leftTranslation G hq y 0 (γ t)
  have hb := ENNReal.add_lt_add
    (show horizontalL2Distance (G.horizontalFields hq) x y < ENNReal.ofReal r from hy) hd'
  change horizontalL2Distance (G.horizontalFields hq) x (G.mul y (γ t)) < _
  apply (horizontalL2Distance_triangle _ x y _).trans_lt
  rw [he]
  exact hb.trans_eq (by rw [← ENNReal.ofReal_add hr.le (by positivity)]; congr 1; ring)

end HeatKernel
