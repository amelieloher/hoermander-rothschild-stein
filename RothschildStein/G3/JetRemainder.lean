-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import Mathlib.Analysis.Calculus.TaylorIntegral
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace RothschildStein.G3

/-- Vanishing jets imply a quantitative pointwise remainder by the
integral Taylor formula (BB pp. 412–413). -/
theorem norm_le_of_vanishing_jets {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : E → F} {y : E} {n : ℕ} {M : ℝ} (_hM : 0 ≤ M)
    (hf : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ (n + 1) f (t • y))
    (hzero : ∀ k ≤ n, iteratedFDeriv ℝ k f 0 = 0)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, ‖iteratedFDeriv ℝ (n + 1) f (t • y)‖ ≤ M) :
    ‖f y‖ ≤ M * ‖y‖ ^ (n + 1) := by
  have he := map_add_eq_sum_add_integral_iteratedFDeriv (x := (0 : E)) (y := y)
    (n := n) (fun t ht => by simpa only [zero_add] using hf t ht)
  have hs : (∑ k ∈ Finset.range (n + 1), (k.factorial : ℝ)⁻¹ •
      iteratedFDeriv ℝ k f 0 (fun _ => y)) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [hzero k (by have h := Finset.mem_range.mp hk; omega),
      zero_apply, smul_zero]
  rw [zero_add, hs, zero_add] at he
  rw [he, norm_smul, Real.norm_eq_abs]
  have hint : ‖∫ t in (0 : ℝ)..1, (1 - t) ^ n •
      iteratedFDeriv ℝ (n + 1) f (t • y) (fun _ => y)‖ ≤ M * ‖y‖ ^ (n + 1) := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const (C := M * ‖y‖ ^ (n + 1))
      (f := fun t : ℝ => (1 - t) ^ n • iteratedFDeriv ℝ (n + 1) f (t • y) (fun _ => y))
      (a := 0) (b := 1) (by
        intro t ht
        rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
        have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt ht.1, ht.2⟩
        rw [norm_smul, Real.norm_eq_abs, abs_pow, abs_of_nonneg (by linarith [ht'.2] : 0 ≤ 1 - t)]
        have hp : (1 - t) ^ n ≤ 1 := pow_le_one₀ (by linarith [ht'.2]) (by linarith [ht'.1])
        have hd := (iteratedFDeriv ℝ (n + 1) f (t • y)).le_opNorm (fun _ => y)
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hd
        exact (mul_le_of_le_one_left (norm_nonneg _) hp).trans
          (hd.trans (mul_le_mul_of_nonneg_right (hbound t ht') (by positivity))))
    simpa only [sub_zero, abs_one, mul_one] using hh
  have hfac : |(n.factorial : ℝ)⁻¹| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    apply inv_le_one_of_one_le₀
    exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos n)
  exact (mul_le_of_le_one_left (norm_nonneg _) hfac).trans (by
    simpa only [zero_add] using hint)
end RothschildStein.G3
