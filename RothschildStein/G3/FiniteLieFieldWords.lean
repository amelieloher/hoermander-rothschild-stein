-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.FiniteLieFields
public import Mathlib.Analysis.Calculus.FDeriv.Linear
@[expose] public section
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.G3

/-- A retained formal nested word gives its actual fixed nested
field bracket on the primitive coefficient domain, independently of the
chosen homogeneous basis (BB Lemma 9.22, pp. 413–414). -/
theorem finiteLieField_word {a s N : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (Ω : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (I : List (Fin a)) (hne : I ≠ []) (hI : wordWeight p I ≤ s)
    {x : Fin N → ℝ} (hx : x ∈ Ω) :
    finiteLieField D X (wordLieElement I) x = wordBracket X I x := by
  ext j
  let q : (Fin N → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj j
  let g : smoothOnFunctions Ω := ⟨q, by
    change ContDiffOn ℝ (⊤ : ℕ∞) q Ω
    exact q.contDiff.contDiffOn⟩
  have hh := differentialWordEvaluation_finiteLieField D Ω X hX (wordLieElement I) g hx
  change (differentialWordEvaluation Ω X hX
    (finitePolynomial (truncatedBracket I : WordCoefficients a s p)) g).val x =
    fderiv ℝ g.val x (finiteLieField D X (wordLieElement I) x) at hh
  rw [differentialWordEvaluation_truncatedBracket Ω X hX I hne hI,
    smoothFieldOperator_apply Ω _ _ g hx] at hh
  have hg : fderiv ℝ g.val x = (ContinuousLinearMap.proj j : (Fin N → ℝ) →L[ℝ] ℝ) :=
    q.fderiv
  unfold fieldDerivative at hh
  rw [hg] at hh
  exact hh.symm
end RothschildStein.G3
