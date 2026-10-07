-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.BCHCocycle
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- Eichler's induction step puts BCH of rational Lie arguments back
in the rational Lie algebra (BB Lemma 9.70, pp. 472–474). -/
theorem finiteBCH_mem_rationalLieAlgebra_of_lower {b n : ℕ} {p : Fin b → ℕ+}
    (hn : 3 ≤ n) (hLow : ∀ j < n, bchComponent j ∈ rationalSeriesLieAlgebra 2)
    {f g : FiniteWordAlgebra b n p}
    (hf : f ∈ rationalCoefficientLieAlgebra b n p)
    (hg : g ∈ rationalCoefficientLieAlgebra b n p) :
    finiteBCH f g ∈ rationalCoefficientLieAlgebra b n p := by
  have hz := eichler_cocycle_eq_zero (𝕜 := ℚ) n hn
    (rationalBCHClass (b := b) (n := n) (p := p))
    (rationalBCHClass_cocycle hn hLow) rationalBCHClass_collinear
    (rationalBCHClass_smul hLow) ⟨f, hf⟩ ⟨g, hg⟩
  exact (Submodule.Quotient.mk_eq_zero _).mp hz

/-- The universal top component is a rational Lie polynomial whenever
all lower universal components are (BB Lemma 9.70, pp. 472–474). -/
theorem bchComponent_mem_rationalLieAlgebra_of_lower (n : ℕ) (hn : 3 ≤ n)
    (hLow : ∀ j < n, bchComponent j ∈ rationalSeriesLieAlgebra 2) :
    bchComponent n ∈ rationalSeriesLieAlgebra 2 := by
  have h0 : finiteLetter (s := n) (p := fun _ : Fin 2 => 1) 0 ∈
      rationalCoefficientLieAlgebra 2 n (fun _ => 1) := LieSubalgebra.subset_lieSpan ⟨0, rfl⟩
  have h1 : finiteLetter (s := n) (p := fun _ : Fin 2 => 1) 1 ∈
      rationalCoefficientLieAlgebra 2 n (fun _ => 1) := LieSubalgebra.subset_lieSpan ⟨1, rfl⟩
  have hb := finiteBCH_mem_rationalLieAlgebra_of_lower hn hLow h0 h1
  rw [← universalFiniteBCH_eq] at hb
  have hp := finiteWeightProjection_mem_rationalLieAlgebra n hb
  have he := finiteExtendLinear_mem_rationalLieAlgebra hp
  change finiteExtendLinear (universalComponent n n) ∈ _ at he
  rw [universalComponent_eq] at he
  have hre := extend_restrict_eq_of_homogeneous (bchComponent_homogeneous n) (s := n) le_rfl
  exact hre ▸ he
end RothschildStein.G3
