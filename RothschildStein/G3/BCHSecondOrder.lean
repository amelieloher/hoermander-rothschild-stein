-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.BCHFirstOrder
public import RothschildStein.G3.LieFiltration
public import Mathlib.Tactic.Module
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- The exponential in the degree-two quotient has its exact quadratic form
(BB Lemma 9.69, p. 471). -/
theorem finiteExp_quadratic {a : ℕ} {p : Fin a → ℕ+}
    {f : FiniteWordAlgebra a 2 p} (hf : FiniteOrderAtLeast 1 f) :
    finiteExp f = 1 + f + (1 / 2 : ℝ) • f ^ 2 := by
  unfold finiteExp
  norm_num [Finset.sum_range_succ, pow_cutoff_eq_zero hf, Nat.factorial, pow_zero, pow_one]

/-- C₂(f,g)=[f,g]/2 in the degree-two quotient
(BB Lemma 9.69, p. 471). -/
theorem finiteBCH_cutoff_two {a : ℕ} {p : Fin a → ℕ+}
    {f g : FiniteWordAlgebra a 2 p} (hf : FiniteOrderAtLeast 1 f)
    (hg : FiniteOrderAtLeast 1 g) :
    finiteBCH f g = f + g + (1 / 2 : ℝ) • ⁅f, g⁆ := by
  let h := f + g + (1 / 2 : ℝ) • ⁅f, g⁆
  have hbr : FiniteOrderAtLeast 2 ⁅f, g⁆ := finiteOrderAtLeast_lie hf hg
  have hcorr := finiteOrderAtLeast_smul hbr (1 / 2 : ℝ)
  have hs := finiteOrderAtLeast_add hf hg
  have hh : FiniteOrderAtLeast 1 h :=
    finiteOrderAtLeast_add hs (finiteOrderAtLeast_mono hcorr (by omega))
  have hd : FiniteOrderAtLeast 2 (h - (f + g)) := by
    simpa only [h, add_sub_cancel_left] using hcorr
  have hsq : h ^ 2 = (f + g) ^ 2 := by
    apply sub_eq_zero.mp
    exact eq_zero_of_finiteOrderAtLeast_gt (finiteOrderAtLeast_pow_sub hh hs hd 1) (by omega)
  have hfg2 : f * g ^ 2 = 0 :=
    eq_zero_of_finiteOrderAtLeast_gt
      (finiteOrderAtLeast_mul hf (finiteOrderAtLeast_pow hg 2)) (by omega)
  have hf2g : f ^ 2 * g = 0 :=
    eq_zero_of_finiteOrderAtLeast_gt
      (finiteOrderAtLeast_mul (finiteOrderAtLeast_pow hf 2) hg) (by omega)
  have hf2g2 : f ^ 2 * g ^ 2 = 0 :=
    eq_zero_of_finiteOrderAtLeast_gt
      (finiteOrderAtLeast_mul (finiteOrderAtLeast_pow hf 2) (finiteOrderAtLeast_pow hg 2)) (by omega)
  have hsum : (f + g) ^ 2 = f ^ 2 + f * g + g * f + g ^ 2 := by noncomm_ring
  apply finiteExp_injective_positive (finiteBCH_order hf hg) hh
  rw [finiteExp_BCH hf hg, finiteExp_quadratic hf, finiteExp_quadratic hg,
    finiteExp_quadratic hh, hsq, hsum]
  simp only [h, Ring.lie_def, mul_add, add_mul, one_mul, mul_one,
    smul_mul_assoc, mul_smul_comm, hfg2, hf2g, hf2g2, smul_zero, add_zero]
  module

end RothschildStein.G3
