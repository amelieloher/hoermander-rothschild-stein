-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.TriangularRepresentation
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace RothschildStein.L1

/-- Appending one base-polynomial coordinate preserves the full
triangular polynomial representation of all earlier coordinates. -/
theorem triangularPolynomialRepresentation_step {a n N : ℕ}
    {X : Fin a → (Fin n → ℝ) → (Fin n → ℝ)}
    {Y : Fin a → (Fin N → ℝ) → (Fin N → ℝ)}
    (h : TriangularPolynomialRepresentation X Y)
    (U : Fin a → MvPolynomial (Fin N) ℝ) :
    TriangularPolynomialRepresentation X
      (oneVariableLift Y (fun j x => MvPolynomial.eval x (U j))) := by
  classical
  obtain ⟨hn,hbase,hpoly⟩ := h
  have hn' : n ≤ N+1 := by omega
  refine ⟨hn',?_,?_⟩
  · intro i ξ j
    have he : Fin.castLE hn' j = Fin.castAdd 1 (Fin.castLE hn j) := by
      apply Fin.ext
      rfl
    rw [he]
    simp only [oneVariableLift,joinPoint,Fin.addCases_left]
    rw [hbase]
    rfl
  · intro i j hj
    revert hj
    refine Fin.addCases ?_ ?_ j
    · intro k hk
      obtain ⟨P,hP,hvars⟩ := hpoly i k (by simpa only [Fin.val_castAdd] using hk)
      refine ⟨MvPolynomial.rename (Fin.castAdd 1) P,?_,?_⟩
      · intro ξ
        simp only [oneVariableLift,joinPoint,Fin.addCases_left]
        rw [hP,MvPolynomial.eval_rename]
        rfl
      · intro l hl
        obtain ⟨v,hv,rfl⟩ := MvPolynomial.mem_vars_rename (Fin.castAdd 1) P hl
        simpa only [Fin.val_castAdd] using hvars v hv
    · intro k _
      refine ⟨MvPolynomial.rename (Fin.castAdd 1) (U i),?_,?_⟩
      · intro ξ
        simp only [oneVariableLift,joinPoint,Fin.addCases_right]
        rw [MvPolynomial.eval_rename]
        rfl
      · intro l hl
        obtain ⟨v,_,rfl⟩ := MvPolynomial.mem_vars_rename (Fin.castAdd 1) (U i) hl
        simp only [Fin.val_castAdd,Fin.val_natAdd]
        omega

/-- Every finite polynomial lift chain has one global triangular
polynomial representation, with exact original horizontal coefficients. -/
theorem PolynomialLiftChain.triangularRepresentation {a n N : ℕ}
    {X : Fin a → (Fin n → ℝ) → (Fin n → ℝ)}
    {Y : Fin a → (Fin N → ℝ) → (Fin N → ℝ)}
    (h : PolynomialLiftChain X Y) : TriangularPolynomialRepresentation X Y := by
  induction h with
  | refl => exact triangularPolynomialRepresentation_refl X
  | step h U ih => exact triangularPolynomialRepresentation_step ih U
end RothschildStein.L1
