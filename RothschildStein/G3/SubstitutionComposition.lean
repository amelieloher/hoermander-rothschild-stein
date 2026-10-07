-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.SubstitutionPolynomial
public import RothschildStein.G3.CompletedBCH
public import RothschildStein.G3.BCHCoefficients
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- Universal associative BCH in two letters evaluates to BCH of any
positive-order pair in a finite coefficient algebra (BB p. 468 and Theorem 9.68,
pp. 469–471). -/
theorem finiteBCH_universal_evaluation {b s : ℕ} {p : Fin b → ℕ+}
    (X : Fin 2 → FiniteWordAlgebra b s p) (hX : ∀ i, FiniteOrderAtLeast 1 (X i)) :
    finiteSubstitutionHom X hX
      (finiteBCH (finiteLetter (a := 2) (s := s) (p := fun _ => 1) 0) (finiteLetter 1)) =
        finiteBCH (X 0) (X 1) := by
  have h := map_finiteBCH (finiteSubstitutionHom X hX)
    (fun _ hp => finiteSubstitutionHom_order X hX hp) (finiteLetter_order 0) (finiteLetter_order 1)
  rw [finiteSubstitutionHom_letter, finiteSubstitutionHom_letter] at h
  exact h
end RothschildStein.G3
