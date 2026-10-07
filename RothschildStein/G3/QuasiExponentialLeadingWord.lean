-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.QuasiExponentialLog
public import RothschildStein.G3.BCHCommutator
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- Formal word coefficients have their exact weighted lower order
(BB Lemma 9.26, pp. 417–419). -/
theorem finiteBracketWord_weight_order {a s : ℕ} (p : Fin a → ℕ+) (I : List (Fin a)) :
    FiniteOrderAtLeast (wordWeight p I) (finiteBracketWord (s := s) (p := p) I) := by
  rw [finiteOrderAtLeast_iff]
  intro J hJ
  exact formalBracket_homogeneous p I J.val (by omega)

/-- Every signed quasi-exponential logarithm has the positive nested
word as its leading weighted term; all other terms have strictly larger weight
(BB Lemma 9.26, pp. 417–419; corrected sign and coefficient induction). -/
theorem quasiExponentialLog_leading {a s : ℕ} {p : Fin a → ℕ+} (hs : 1 ≤ s)
    (I : List (Fin a)) :
    FiniteOrderAtLeast (wordWeight p I) (quasiExponentialLog (s := s) (p := p) I).val ∧
    FiniteOrderAtLeast (wordWeight p I + 1)
      ((quasiExponentialLog (s := s) (p := p) I).val - finiteBracketWord I) := by
  induction I with
  | nil => exact ⟨finiteOrderAtLeast_zero_element _, by
      change FiniteOrderAtLeast 1 (0 - 0 : FiniteWordAlgebra a s p)
      simp only [sub_self]
      exact finiteOrderAtLeast_zero_element 1⟩
  | cons i I ih =>
    cases I with
    | nil => exact ⟨finiteBracketWord_weight_order p [i], by
        change FiniteOrderAtLeast _ (finiteBracketWord [i] - finiteBracketWord [i])
        rw [sub_self]
        exact finiteOrderAtLeast_zero_element _⟩
    | cons j I =>
      let A : FiniteWordAlgebra a s p := finiteLetter i
      let B : FiniteWordAlgebra a s p := (quasiExponentialLog (s := s) (p := p) (j :: I)).val
      have hA : FiniteOrderAtLeast (p i : ℕ) A := by
        change FiniteOrderAtLeast (p i : ℕ) (finiteBracketWord (s := s) (p := p) [i])
        simpa only [wordWeight, List.map_singleton, List.sum_singleton] using
          finiteBracketWord_weight_order (s := s) p [i]
      have hk : 1 ≤ (p i : ℕ) := (p i).pos
      have hl : 1 ≤ wordWeight p (j :: I) := by
        have h := length_le_weight p (j :: I)
        simp only [List.length_cons] at h
        omega
      have hval : (quasiExponentialLog (s := s) (p := p) (i :: j :: I)).val =
          finiteBCH (finiteBCH (finiteBCH A B) (-A)) (-B) := rfl
      have hw : wordWeight p (i :: j :: I) = (p i : ℕ) + wordWeight p (j :: I) := by
        simp only [wordWeight, List.map_cons, List.sum_cons]
      rw [hval, hw]
      refine ⟨finiteBCH_commutator_order hk hl hA ih.1, ?_⟩
      have he : finiteBCH (finiteBCH (finiteBCH A B) (-A)) (-B) - finiteBracketWord (i :: j :: I) =
          (finiteBCH (finiteBCH (finiteBCH A B) (-A)) (-B) - ⁅A,B⁆) +
            ⁅A, B - finiteBracketWord (j :: I)⁆ := by
        rw [← coefficient_nested_cons, lie_sub]
        change _ - ⁅A, finiteBracketWord (j :: I)⁆ = _
        abel
      rw [he]
      exact finiteOrderAtLeast_add (finiteBCH_commutator_sub_lie_order hs hk hl hA ih.1)
        (by simpa only [Nat.add_assoc] using finiteOrderAtLeast_lie hA ih.2)
end RothschildStein.G3
