-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.NonformalTangentRelation
public import RothschildStein.G3.Homogeneity
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators
namespace RothschildStein.L1

/-- The nonzero coefficient used for the new vertical
jet belongs to a nonempty word (BB Proposition 10.17, pp. 490–492). -/
theorem exists_nonempty_formal_relation_coefficient {a s : ℕ} {p : Fin a → ℕ+}
    (c : WordCoefficients a s p) (hnot : ¬ FormalRelation c) :
    ∃ J : BoundedWord a s p, boundedWordList J ≠ [] ∧
      (∑ I, c I * truncatedBracket (boundedWordList I) J) ≠ 0 := by
  classical
  obtain ⟨J,hJ⟩ := exists_nonzero_formal_relation_coefficient c hnot
  refine ⟨J,?_,hJ⟩
  intro he
  apply hJ
  simp only [truncatedBracket,he,G3.formalBracket_constant_zero,mul_zero,Finset.sum_const_zero]

/-- A Kronecker prescription detects the selected
nonzero formal coefficient, with the empty-word value zero (BB (10.8)). -/
theorem exists_vertical_jet_prescription {a s : ℕ} {p : Fin a → ℕ+}
    (c : WordCoefficients a s p) (hnot : ¬ FormalRelation c) :
    ∃ d : List (Fin a) → ℝ, d [] = 0 ∧
      (∑ I, c I * ∑ J : BoundedWord a s p,
        truncatedBracket (boundedWordList I) J * d (boundedWordList J)) ≠ 0 := by
  classical
  obtain ⟨J,hne,hJ⟩ := exists_nonempty_formal_relation_coefficient c hnot
  let d : List (Fin a) → ℝ := fun K => if K = boundedWordList J then 1 else 0
  refine ⟨d,?_,?_⟩
  · simp only [d,ite_eq_right_iff]
    intro h
    exact False.elim (hne h.symm)
  · have he : ∀ K : BoundedWord a s p, d (boundedWordList K) = if K = J then 1 else 0 := by
      intro K
      have hi : boundedWordList K = boundedWordList J ↔ K = J := by
        constructor
        · exact Subtype.ext
        · exact congrArg boundedWordList
      simp only [d,hi]
    simpa only [he,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true] using hJ
end RothschildStein.L1
