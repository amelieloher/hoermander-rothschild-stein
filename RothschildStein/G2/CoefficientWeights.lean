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
open MvPolynomial
variable {N : ℕ} (G : HomogeneousGroup N)

/-- The left canonical coefficient has real degree equal to the difference of weights
(BB Theorem 3.29, pp. 110–111). -/
theorem leftCoefficient_eval_dilate (i k : Fin N) (t : ℝ) (ht : 0 < t)
    (x : Fin N → ℝ) :
    eval (G.dilate t x) (leftCoefficient G i k) =
      t ^ ((G.weight k : ℝ) - G.weight i) * eval x (leftCoefficient G i k) := by
  have h := congrFun (canonicalField_homogeneous G i t ht x) k
  simp only [canonicalField_coordinate, HomogeneousGroup.dilate, coordinateDilation,
    Pi.smul_apply, smul_eq_mul] at h
  apply mul_left_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos ht (G.weight i : ℝ)))
  rw [← _root_.mul_assoc, ← Real.rpow_add ht]
  have he : (G.weight i : ℝ) + ((G.weight k : ℝ) - G.weight i) = G.weight k := by ring
  rw [he]
  simpa only [HomogeneousGroup.dilate, Real.rpow_natCast] using h.symm

/-- For increasing weights the coefficient is a weighted homogeneous polynomial
(BB Theorem 3.29, pp. 110–111). -/
theorem leftCoefficient_weightedHomogeneous (i k : Fin N) (h : G.weight i ≤ G.weight k) :
    (leftCoefficient G i k).IsWeightedHomogeneous G.weight (G.weight k - G.weight i) := by
  apply weightedHomogeneous_of_eval_dilate
  intro t ht x
  have he := leftCoefficient_eval_dilate G i k t ht x
  rw [← Nat.cast_sub h, Real.rpow_natCast] at he
  exact he

/-- A coefficient with decreasing weights is zero (BB Theorem 3.29, p. 110). -/
theorem leftCoefficient_zero_of_weight_lt (i k : Fin N) (h : G.weight k < G.weight i) :
    leftCoefficient G i k = 0 := by
  obtain hz | ⟨n, hn, _⟩ := weightedHomogeneous_of_real_eval_dilate G.weight
    (leftCoefficient G i k) ((G.weight k : ℝ) - G.weight i)
    (fun t ht x => leftCoefficient_eval_dilate G i k t ht x)
  · exact hz
  · have hc : (G.weight k : ℝ) < G.weight i := by exact_mod_cast h
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith

end RothschildStein.G2
