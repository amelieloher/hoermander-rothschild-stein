-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.RationalBCH
@[expose] public section
noncomputable section
open scoped BigOperators
namespace RothschildStein.G3

/-- A rational universal Lie polynomial evaluates into the real
Lie algebra whenever its arguments lie there (BB Proposition 10.42, p. 524). -/
theorem finiteSubstitution_mem_realLieAlgebra {a b s : ℕ} {p : Fin b → ℕ+}
    (X : Fin a → FiniteWordAlgebra b s p) (hX : ∀ i, FiniteOrderAtLeast 1 (X i))
    (hXL : ∀ i, X i ∈ finiteLieSpan b s p)
    {f : FiniteWordAlgebra a s (fun _ => 1)}
    (hf : f ∈ rationalCoefficientLieAlgebra a s (fun _ => 1)) :
    finiteSubstitutionHom X hX f ∈ finiteLieSpan b s p := by
  let F := (finiteSubstitutionHom X hX).restrictScalars ℚ
  have hle : rationalCoefficientLieAlgebra a s (fun _ => 1) ≤
      (realCoefficientSpanOverRat b s p).comap F.toLieHom := by
    apply LieSubalgebra.lieSpan_le.mpr
    rintro _ ⟨i, rfl⟩
    change finiteSubstitutionHom X hX (finiteLetter i) ∈ finiteLieSpan b s p
    rw [finiteSubstitutionHom_letter]
    exact hXL i
  exact hle hf

/-- The weighted finite free Lie carrier is closed under BCH
(BB Proposition 10.42, pp. 523–524). -/
theorem finiteLieSpan_bch_mem {a s : ℕ} {p : Fin a → ℕ+}
    {f g : FiniteWordAlgebra a s p} (hf : f ∈ finiteLieSpan a s p)
    (hg : g ∈ finiteLieSpan a s p) : finiteBCH f g ∈ finiteLieSpan a s p := by
  have hfp := formalSpan_positive_order f hf
  have hgp := formalSpan_positive_order g hg
  have he := finiteBCH_components (bchPair f g) (bchPair_prop hfp hgp)
  simp only [bchPair, ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false] at he
  rw [he]
  apply Submodule.sum_mem
  intro j _
  exact finiteSubstitution_mem_realLieAlgebra _ _ (bchPair_prop hf hg)
    (universalComponent_mem_rationalLieAlgebra s j)
end RothschildStein.G3
