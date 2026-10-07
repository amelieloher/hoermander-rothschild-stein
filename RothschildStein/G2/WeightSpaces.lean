-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.FieldHomogeneity
public import RothschildStein.G2.InvariantBracket

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

@[expose] public section
noncomputable section
namespace RothschildStein.G2
variable {N : ℕ} (G : HomogeneousGroup N)

/-- The tangent weight space: only coordinates of weight `degree` may be nonzero
(BB Proposition 3.35, p. 114). -/
def tangentWeightSpace (degree : ℝ) : Submodule ℝ (Fin N → ℝ) where
  carrier := {v | ∀ j, (G.weight j : ℝ) ≠ degree → v j = 0}
  zero_mem' := by simp
  add_mem' := by intro v w hv hw j hj; simp [hv j hj, hw j hj]
  smul_mem' := by intro c v hv j hj; simp [hv j hj]

/-- Homogeneity of an invariant field is equivalent to membership in one weight space
(BB Lemma 3.34, p. 113). -/
theorem leftField_homogeneous_iff (v : Fin N → ℝ) (degree : ℝ) :
    IsHomogeneousField G (leftField G v) degree ↔ v ∈ tangentWeightSpace G degree := by
  constructor
  · intro h j hj
    have he := congrFun (h 2 (by norm_num) 0) j
    simp only [dilate_zero, leftField_zero] at he
    simp only [HomogeneousGroup.dilate, coordinateDilation,
      Pi.smul_apply, smul_eq_mul] at he
    by_contra hv
    have hp : (2 : ℝ) ^ (G.weight j : ℝ) = (2 : ℝ) ^ degree := by
      rw [Real.rpow_natCast]
      exact (mul_right_cancel₀ hv he)
    exact hj ((Real.rpow_right_inj (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1)).mp hp)
  · intro h t ht x
    rw [dilate_leftField G t ht]
    have hv : G.dilate t v = t ^ degree • v := by
      ext j
      by_cases hj : (G.weight j : ℝ) = degree
      · simp [HomogeneousGroup.dilate, coordinateDilation, ← hj, Real.rpow_natCast]
      · simp [HomogeneousGroup.dilate, coordinateDilation, h j hj]
    rw [hv]
    exact map_smul (fderiv ℝ (G.mul (G.dilate t x)) 0) _ _

/-- A nonzero homogeneous invariant field has degree among the coordinate weights
(BB Lemma 3.34, p. 113). -/
theorem leftField_homogeneous_degree {v : Fin N → ℝ} (hv : v ≠ 0) {degree : ℝ}
    (h : IsHomogeneousField G (leftField G v) degree) :
    ∃ j, (G.weight j : ℝ) = degree := by
  by_contra hn
  apply hv
  ext j
  exact (leftField_homogeneous_iff G v degree).mp h j (by aesop)

end RothschildStein.G2
