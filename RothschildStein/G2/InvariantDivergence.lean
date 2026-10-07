-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.OppositeGroup
public import RothschildStein.Definitions.fieldTranspose
public import Hormander.F.Transpose

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

@[expose] public section
noncomputable section
namespace RothschildStein.G2
open MvPolynomial
open scoped BigOperators
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Canonical coefficients only use variables preceding their output coordinate
(BB Theorem 3.29, pp. 110–111). -/
theorem leftCoefficient_vars_lt (i k : Fin N) {j : Fin N}
    (hj : j ∈ (leftCoefficient G i k).vars) : j < k := by
  by_cases h : G.weight i ≤ G.weight k
  · obtain ⟨d, hd, hjd⟩ := (mem_vars_iff_mem_support j).mp hj
    have hw := leftCoefficient_weightedHomogeneous G i k h (mem_support_iff.mp hd)
    have hle := Finsupp.le_weight_of_ne_zero' G.weight (Finsupp.mem_support_iff.mp hjd)
    have hpos := G.weight_pos i
    have hjk : G.weight j < G.weight k := by omega
    exact lt_of_not_ge fun hkj => (not_le_of_gt hjk) (G.weight_mono hkj)
  · rw [leftCoefficient_zero_of_weight_lt G i k (by omega)] at hj
    simp at hj

/-- Each canonical coefficient is independent of its output coordinate
(BB Theorem 3.29, p. 111). -/
theorem leftCoefficient_pderiv_self (i k : Fin N) :
    pderiv k (leftCoefficient G i k) = 0 :=
  pderiv_eq_zero_of_notMem_vars fun h => (lt_irrefl k) (leftCoefficient_vars_lt G i k h)

/-- Polynomial coordinates of a prescribed invariant field. -/
def leftFieldPolynomial (v : Fin N → ℝ) (k : Fin N) : MvPolynomial (Fin N) ℝ :=
  ∑ i, C (v i) * leftCoefficient G i k

/-- All invariant fields have polynomial coordinates (BB Proposition 3.26, p. 110). -/
theorem leftField_polynomial (v x : Fin N → ℝ) (k : Fin N) :
    leftField G v x k = eval x (leftFieldPolynomial G v k) := by
  have h := (leftField_invariant G v).canonical_expansion G x
  rw [leftField_zero] at h
  have hc := congrFun h k
  simpa [leftFieldPolynomial, canonicalField_coordinate] using hc

/-- Every left-invariant field has zero divergence
(BB Remark 3.30, p. 111). -/
theorem leftField_divergence_zero (v x : Fin N → ℝ) :
    Hormander.Interface.euclideanDivergence (leftField G v) x = 0 := by
  have he : leftField G v = fun x k => eval x (leftFieldPolynomial G v k) := by
    funext x k
    exact leftField_polynomial G v x k
  have hd := hasFDerivAt_pi.mpr (fun k => hasFDerivAt_eval (leftFieldPolynomial G v k) x)
  rw [he]
  unfold Hormander.Interface.euclideanDivergence
  rw [hd.fderiv]
  apply Finset.sum_eq_zero
  intro k hk
  have hp : pderiv k (leftFieldPolynomial G v k) = 0 := by
    simp [leftFieldPolynomial, map_sum, leftCoefficient_pderiv_self]
  have hc := fderiv_eval_single (leftFieldPolynomial G v k) x k
  rw [(hasFDerivAt_eval (leftFieldPolynomial G v k) x).fderiv, hp] at hc
  simpa [Hormander.Interface.basisVec] using hc

/-- The formal transpose of an invariant field is its negative action
(BB (3.14), p. 111). -/
theorem leftField_transpose (v : Fin N → ℝ) (φ : (Fin N → ℝ) → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x : Fin N → ℝ) :
    fieldTranspose (leftField G v) φ x = -fieldDerivative (leftField G v) φ x := by
  have h := Hormander.F.firstOrderTranspose_formula isOpen_univ (leftField G v)
    (contDiff_leftField G v).contDiffOn φ hφ (Set.subset_univ _) x
  simpa [fieldTranspose, fieldDerivative, leftField_divergence_zero] using h

end RothschildStein.G2
