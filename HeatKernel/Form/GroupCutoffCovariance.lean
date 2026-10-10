-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Geometry.SmoothBallCutoff
public import RothschildStein.G2.TransposeHomogeneity
public import RothschildStein.G2.TransposeInvariance

import Mathlib.Tactic.Linter

/-! # Translation and dilation of smooth horizontal cutoffs -/

@[expose] public section

noncomputable section

open Set RothschildStein RothschildStein.G2

namespace HeatKernel

/-- A scalar function transported from the unit scale to a ball centered at a group point. -/
def translatedDilatedFunction {N : ℕ} (G : HomogeneousGroup N) (x : Fin N → ℝ)
    (r : ℝ) (f : (Fin N → ℝ) → ℝ) : (Fin N → ℝ) → ℝ :=
  (f ∘ G.dilate r⁻¹) ∘ G.mul (G.inv x)

/-- Each weight-one horizontal derivative of a transported function scales by the inverse
radius and is transported by the same group map. -/
theorem fieldDerivative_translatedDilatedFunction {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q ≤ N) (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (x : Fin N → ℝ) {r : ℝ} (hr : 0 < r) {f : (Fin N → ℝ) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin q) (z : Fin N → ℝ) :
    fieldDerivative (G.horizontalFields hq i) (translatedDilatedFunction G x r f) z =
      r⁻¹ * fieldDerivative (G.horizontalFields hq i) f (G.dilate r⁻¹ (G.mul (G.inv x) z)) := by
  have hleft : IsLeftInvariantField G (G.horizontalFields hq i) := by
    simpa only [HomogeneousGroup.horizontalFields, canonicalField_eq_leftField] using
      leftField_invariant G (Hormander.Interface.basisVec (Fin.castLE hq i))
  have ht := congrFun (hleft.operator G (f ∘ G.dilate r⁻¹)
    (hf.comp (contDiff_dilate G r⁻¹)) (G.inv x)) z
  have hd := (isHomogeneousField_iff_operator G (G.canonicalField (Fin.castLE hq i))
    (G.weight (Fin.castLE hq i))).mp (canonicalField_homogeneous G (Fin.castLE hq i))
    f hf r⁻¹ (inv_pos.mpr hr) (G.mul (G.inv x) z)
  exact ht.trans (by simpa only [HomogeneousGroup.horizontalFields, hw i, Nat.cast_one,
    Real.rpow_one, Function.comp_def] using hd)

end HeatKernel
