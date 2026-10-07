-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.BCHLieInduction
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- Every universal homogeneous BCH coefficient is a rational Lie
polynomial, with no formal analytic convergence hypothesis (BB Lemma 9.70,
pp. 471–474). -/
theorem bchComponent_mem_rationalSeriesLieAlgebra (n : ℕ) :
    bchComponent n ∈ rationalSeriesLieAlgebra 2 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have h0 : letterSeries (0 : Fin 2) ∈ rationalSeriesLieAlgebra 2 :=
      LieSubalgebra.subset_lieSpan ⟨0, rfl⟩
    have h1 : letterSeries (1 : Fin 2) ∈ rationalSeriesLieAlgebra 2 :=
      LieSubalgebra.subset_lieSpan ⟨1, rfl⟩
    by_cases hn : 3 ≤ n
    · exact bchComponent_mem_rationalLieAlgebra_of_lower n hn ih
    · interval_cases n
      · rw [bchComponent_zero]
        exact (rationalSeriesLieAlgebra 2).zero_mem
      · rw [bchComponent_one]
        exact (rationalSeriesLieAlgebra 2).add_mem h0 h1
      · rw [bchComponent_two]
        have he : (formalBracket [0, 1] : CoefficientSeries 2) =
            ⁅letterSeries (0 : Fin 2), letterSeries (1 : Fin 2)⁆ :=
          (nested_eval_formalBracket (Nested.bracket (0 : Fin 2) (.letter 1))).symm
        rw [he]
        have hr : (1 / 2 : ℝ) • ⁅letterSeries (0 : Fin 2), letterSeries (1 : Fin 2)⁆ =
            (1 / 2 : ℚ) • ⁅letterSeries (0 : Fin 2), letterSeries (1 : Fin 2)⁆ := by
          have h := ratCast_smul_eq ℚ ℝ (1 / 2) ⁅letterSeries (0 : Fin 2), letterSeries (1 : Fin 2)⁆
          norm_num at h ⊢
          exact h.symm
        have hm := (rationalSeriesLieAlgebra 2).smul_mem (1 / 2 : ℚ)
          ((rationalSeriesLieAlgebra 2).lie_mem h0 h1)
        exact hr.symm ▸ hm

/-- The finite universal coefficients remain rational Lie polynomials
(BB Lemma 9.70 and Proposition 10.42, pp. 472, 524). -/
theorem universalComponent_mem_rationalLieAlgebra (s n : ℕ) :
    universalComponent s n ∈ rationalCoefficientLieAlgebra 2 s (fun _ => 1) := by
  rw [universalComponent_eq]
  exact truncateSeries_mem_rationalLieAlgebra (bchComponent_mem_rationalSeriesLieAlgebra n)
end RothschildStein.G3
