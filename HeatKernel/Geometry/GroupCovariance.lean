-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Geometry.CurveCovariance
public import RothschildStein.G2.FieldHomogeneity
public import RothschildStein.Definitions.HomogeneousGroup.horizontalFields

/-! Translation invariance and dilation covariance of the horizontal length distance. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open RothschildStein RothschildStein.G2
open scoped NNReal
namespace HeatKernel

/-- Left translations preserve the horizontal control distance. -/
theorem horizontalL2Distance_leftTranslation {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N)
    (g x y : Fin N → ℝ) :
    horizontalL2Distance (G.horizontalFields hq) (G.mul g x) (G.mul g y) =
      horizontalL2Distance (G.horizontalFields hq) x y := by
  have hle : ∀ g x y, horizontalL2Distance (G.horizontalFields hq) (G.mul g x) (G.mul g y) ≤
      horizontalL2Distance (G.horizontalFields hq) x y := by
    intro g x y
    have hb := horizontalL2Distance_map_le ((contDiff_leftTranslation G g).of_le (by simp))
      (by norm_num : (0 : ℝ) < 1) (X := G.horizontalFields hq) (Y := G.horizontalFields hq)
      (fun i z => by simpa only [one_smul, HomogeneousGroup.horizontalFields, canonicalField_eq_leftField] using (leftField_invariant G
          (Hormander.Interface.basisVec (Fin.castLE hq i)) g z)) x y
    simpa only [ENNReal.ofReal_one, one_mul] using hb
  apply le_antisymm (hle g x y)
  simpa only [← G2.mul_assoc, G2.inv_mul, G2.zero_mul] using hle (G.inv g) (G.mul g x) (G.mul g y)

/-- A positive coordinate dilation multiplies the horizontal distance by its factor
when the selected fields all have weight one. -/
theorem horizontalL2Distance_dilate {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1) {r : ℝ} (hr : 0 < r)
    (x y : Fin N → ℝ) :
    horizontalL2Distance (G.horizontalFields hq) (G.dilate r x) (G.dilate r y) =
      ENNReal.ofReal r * horizontalL2Distance (G.horizontalFields hq) x y := by
  have hle : ∀ r : ℝ, 0 < r → ∀ x y,
      horizontalL2Distance (G.horizontalFields hq) (G.dilate r x) (G.dilate r y) ≤
        ENNReal.ofReal r * horizontalL2Distance (G.horizontalFields hq) x y := by
    intro r hr x y
    apply horizontalL2Distance_map_le ((contDiff_dilate G r).of_le (by simp)) hr
    intro i z
    rw [(hasFDerivAt_dilate G r z).fderiv, dilationDifferential_apply]
    have hh := canonicalField_homogeneous G (Fin.castLE hq i) r hr z
    simpa only [HomogeneousGroup.horizontalFields, hw i, Nat.cast_one, Real.rpow_one] using hh
  apply le_antisymm (hle r hr x y)
  have hb := hle r⁻¹ (inv_pos.mpr hr) (G.dilate r x) (G.dilate r y)
  rw [dilate_inv_dilate G hr.ne', dilate_inv_dilate G hr.ne'] at hb
  calc
    ENNReal.ofReal r * horizontalL2Distance (G.horizontalFields hq) x y ≤
        ENNReal.ofReal r * (ENNReal.ofReal r⁻¹ *
          horizontalL2Distance (G.horizontalFields hq) (G.dilate r x) (G.dilate r y)) :=
      mul_le_mul le_rfl hb bot_le bot_le
    _ = _ := by rw [← _root_.mul_assoc, ← ENNReal.ofReal_mul hr.le, mul_inv_cancel₀ hr.ne',
      ENNReal.ofReal_one, one_mul]

end HeatKernel
