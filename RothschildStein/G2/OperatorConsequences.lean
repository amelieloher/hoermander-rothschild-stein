-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.FieldHomogeneity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

@[expose] public section
noncomputable section
namespace RothschildStein.G2
variable {N : ℕ} (G : HomogeneousGroup N)

/-- The coefficient characterization of vector-field homogeneity
(BB Proposition 3.23, p. 107). -/
theorem isHomogeneousField_iff_coefficients
    (V : (Fin N → ℝ) → (Fin N → ℝ)) (β : ℝ) :
    IsHomogeneousField G V β ↔ ∀ j t, 0 < t → ∀ x,
      V (G.dilate t x) j = t ^ ((G.weight j : ℝ) - β) * V x j := by
  constructor
  · intro h j t ht x
    have he := congrFun (h t ht x) j
    apply mul_left_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos ht β))
    rw [← _root_.mul_assoc, ← Real.rpow_add ht]
    have hb : β + ((G.weight j : ℝ) - β) = G.weight j := by ring
    rw [hb, Real.rpow_natCast]
    exact he.symm
  · intro h t ht x
    ext j
    change t ^ G.weight j * V x j = t ^ β * V (G.dilate t x) j
    rw [h j t ht x, ← _root_.mul_assoc, ← Real.rpow_add ht]
    have hb : β + ((G.weight j : ℝ) - β) = G.weight j := by ring
    rw [hb, Real.rpow_natCast]

/-- Coordinate differentiation has its coordinate weight as degree
(BB p. 107). -/
theorem coordinateDerivative_homogeneous (j : Fin N) :
    IsHomogeneousOperator G
      (fieldDerivative (fun _ => Hormander.Interface.basisVec j)) (G.weight j) := by
  apply (isHomogeneousField_iff_operator G _ _).mp
  intro t ht x
  ext k
  simp [HomogeneousGroup.dilate, coordinateDilation, Hormander.Interface.basisVec,
    Pi.single_apply, Real.rpow_natCast]
  split_ifs <;> simp_all

end RothschildStein.G2
