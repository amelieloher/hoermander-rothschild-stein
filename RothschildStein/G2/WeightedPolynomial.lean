-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Algebra.MvPolynomial.Variables
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
namespace RothschildStein.G2
open MvPolynomial
open scoped BigOperators Classical
variable {ι : Type*}

/-- Coefficient scaling by the weight of each monomial. -/
def weightedScale (w : ι → ℕ) (t : ℝ) (p : MvPolynomial ι ℝ) : MvPolynomial ι ℝ :=
  ∑ d ∈ p.support, monomial d (t ^ Finsupp.weight w d * p.coeff d)

/-- The coefficient formula for weighted scaling. -/
theorem coeff_weightedScale (w : ι → ℕ) (t : ℝ) (p : MvPolynomial ι ℝ)
    (d : ι →₀ ℕ) : (weightedScale w t p).coeff d = t ^ Finsupp.weight w d * p.coeff d := by
  classical
  simp only [weightedScale, coeff_sum, coeff_monomial]
  by_cases h : d ∈ p.support
  · simp [h]
  · simp [h, notMem_support_iff.mp h]

/-- Scaling all variables scales a monomial by its weighted degree. -/
theorem eval_weightedScale (w : ι → ℕ) (t : ℝ) (p : MvPolynomial ι ℝ) (z : ι → ℝ) :
    eval z (weightedScale w t p) = eval (fun i => t ^ w i * z i) p := by
  classical
  rw [eval_eq (fun i => t ^ w i * z i) p]
  simp only [weightedScale, map_sum, eval_monomial, Finsupp.prod]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [mul_pow, Finset.prod_mul_distrib, ← pow_mul,
    Finset.prod_pow_eq_pow_sum, Finsupp.weight_apply, Finsupp.sum, smul_eq_mul]
  have hw : (∑ i ∈ d.support, d i * w i) = ∑ i ∈ d.support, w i * d i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact Nat.mul_comm _ _
  rw [hw]
  ring

/-- Dilation homogeneity of natural degree implies weighted homogeneity (BB p. 97). -/
theorem weightedHomogeneous_of_eval_dilate (w : ι → ℕ) (p : MvPolynomial ι ℝ) (m : ℕ)
    (h : ∀ t : ℝ, 0 < t → ∀ z : ι → ℝ,
      eval (fun i => t ^ w i * z i) p = t ^ m * eval z p) :
    p.IsWeightedHomogeneous w m := by
  classical
  have hs : weightedScale w 2 p = C ((2 : ℝ) ^ m) * p := by
    apply MvPolynomial.funext
    intro z
    rw [eval_weightedScale, h 2 (by norm_num), map_mul, eval_C]
  intro d hd
  have hc := congrArg (fun q : MvPolynomial ι ℝ => q.coeff d) hs
  rw [coeff_weightedScale, coeff_C_mul] at hc
  have he := mul_right_cancel₀ hd hc
  exact (pow_right_injective₀ (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)) he

/-- A nonzero dilation-homogeneous polynomial has natural weighted degree,
including when its scaling degree was specified as a real number (BB p. 97). -/
theorem weightedHomogeneous_of_real_eval_dilate (w : ι → ℕ) (p : MvPolynomial ι ℝ) (m : ℝ)
    (h : ∀ t : ℝ, 0 < t → ∀ z : ι → ℝ,
      eval (fun i => t ^ w i * z i) p = t ^ m * eval z p) :
    p = 0 ∨ ∃ n : ℕ, m = n ∧ p.IsWeightedHomogeneous w n := by
  classical
  by_cases hp : p = 0
  · exact Or.inl hp
  right
  have hs : weightedScale w 2 p = C ((2 : ℝ) ^ m) * p := by
    apply MvPolynomial.funext
    intro z
    rw [eval_weightedScale, h 2 (by norm_num), map_mul, eval_C]
  have hdg : ∀ d, p.coeff d ≠ 0 → (Finsupp.weight w d : ℝ) = m := by
    intro d hd
    have hc := congrArg (fun q : MvPolynomial ι ℝ => q.coeff d) hs
    rw [coeff_weightedScale, coeff_C_mul] at hc
    have he := mul_right_cancel₀ hd hc
    rw [← Real.rpow_natCast] at he
    exact (Real.rpow_right_inj (by norm_num) (by norm_num)).mp he
  obtain ⟨d, hd⟩ := MvPolynomial.exists_coeff_ne_zero hp
  refine ⟨Finsupp.weight w d, (hdg d hd).symm, ?_⟩
  intro e he
  exact Nat.cast_injective ((hdg e he).trans (hdg d hd).symm)

end RothschildStein.G2
