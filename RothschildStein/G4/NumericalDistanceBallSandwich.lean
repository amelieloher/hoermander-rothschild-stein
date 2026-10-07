-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G4.ControlTopology
public import RothschildStein.G4.AuxiliaryControl
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped ENNReal
namespace RothschildStein.G4

/-- The numerical pointwise comparison yields the actual ball
sandwich with strict ball membership (BB p. 405). -/
theorem ordinary_auxiliary_ball_sandwich_of_distance_bound {m n s : ℕ}
    (Ω : Set (Fin n → ℝ)) (w : Fin m → ℕ+)
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (hw : ∀ i, (w i : ℕ) ≤ s)
    (x : Fin n → ℝ) {C A ε r : ℝ} (hC : 0 < C) (hA : 1 ≤ A)
    (hAC : 2*C ≤ A) (hr : 0 < r) (hrε : r < ε)
    (hcomp : ∀ y, auxiliaryDistance (s := s) Ω w X x y < ENNReal.ofReal ε →
      controlDistance Ω w X x y ≤ ENNReal.ofReal C * auxiliaryDistance (s := s) Ω w X x y) :
    {y | auxiliaryDistance (s := s) Ω w X x y < ENNReal.ofReal (r/A)} ⊆
      controlBall Ω w X x r ∧
    controlBall Ω w X x r ⊆ {y | auxiliaryDistance (s := s) Ω w X x y < ENNReal.ofReal r} := by
  have hAp : 0 < A := zero_lt_one.trans_le hA
  have hδ : 0 < r/A := div_pos hr hAp
  have hδr : r/A ≤ r := div_le_self hr.le hA
  constructor
  · intro y hy
    have hd := hcomp y (hy.trans_le (ENNReal.ofReal_le_ofReal (hδr.trans hrε.le)))
    have hCr : C*(r/A) < r := by
      have he : A*(r/A) = r := by field_simp
      have hh := mul_le_mul_of_nonneg_right hAC hδ.le
      nlinarith
    have hc : controlDistance Ω w X x y ≤ ENNReal.ofReal (C*(r/A)) := by
      rw [ENNReal.ofReal_mul hC.le]
      exact hd.trans (mul_le_mul' le_rfl hy.le)
    exact hc.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hr).mpr hCr)
  · intro y hy
    exact (auxiliaryDistance_le Ω w X hw x y).trans_lt hy
end RothschildStein.G4
