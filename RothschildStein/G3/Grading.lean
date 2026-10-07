-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.Homogeneity
public import RothschildStein.G3.Truncation
@[expose] public section
noncomputable section
open scoped BigOperators
namespace RothschildStein.G3

/-- Projection onto one weighted layer of the finite carrier (BB (10.50), p. 523). -/
def weightProjection {a s : ℕ} {p : Fin a → ℕ+} (k : ℕ) :
    WordCoefficients a s p →ₗ[ℝ] WordCoefficients a s p where
  toFun f J := if wordWeight p J.val = k then f J else 0
  map_add' f g := by funext J; by_cases h : wordWeight p J.val = k <;> simp [h]
  map_smul' r f := by funext J; by_cases h : wordWeight p J.val = k <;> simp [h]

/-- Projection selects exactly the weight of a formal commutator
(BB (10.51), p. 524). -/
theorem weightProjection_truncatedBracket {a s : ℕ} {p : Fin a → ℕ+}
    (k : ℕ) (I : List (Fin a)) :
    weightProjection k (truncatedBracket I : WordCoefficients a s p) =
      if wordWeight p I = k then truncatedBracket I else 0 := by
  funext J
  by_cases hI : wordWeight p I = k
  · simp only [hI, ite_true]
    change (if wordWeight p J.val = k then formalBracket I J.val else 0) = _
    by_cases hJ : wordWeight p J.val = k
    · simp [hJ, truncatedBracket, boundedWordList]
    · rw [ite_eq_right hJ]
      exact (formalBracket_homogeneous p I J.val (by simpa only [hI] using hJ)).symm
  · simp only [hI, ite_false]
    change (if wordWeight p J.val = k then formalBracket I J.val else 0) = 0
    by_cases hJ : wordWeight p J.val = k
    · rw [ite_eq_left hJ]
      exact formalBracket_homogeneous p I J.val (by omega)
    · rw [ite_eq_right hJ]

/-- Each homogeneous component of the Lie span remains in that span
(BB Proposition 10.42, p. 523). -/
theorem weightProjection_mem_formalSpan {a s : ℕ} {p : Fin a → ℕ+}
    (k : ℕ) {f : WordCoefficients a s p} (hf : f ∈ formalSpan a s p) :
    weightProjection k f ∈ formalSpan a s p := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨I, hne, hI, rfl⟩ := hg
    rw [weightProjection_truncatedBracket]
    split
    · exact truncatedBracket_mem_span I hne hI
    · exact Submodule.zero_mem _
  | zero => simpa only [map_zero] using (formalSpan a s p).zero_mem
  | add f g _ _ hf hg => rw [map_add]; exact Submodule.add_mem _ hf hg
  | smul r f _ hf => rw [map_smul]; exact Submodule.smul_mem _ r hf

/-- The finite carrier is the sum of all its weighted projections
(BB (10.50), pp. 523–525). -/
theorem sum_weightProjection {a s : ℕ} {p : Fin a → ℕ+}
    (f : WordCoefficients a s p) : (∑ k ∈ Finset.range (s + 1), weightProjection k f) = f := by
  funext J
  simp only [Finset.sum_apply]
  change (∑ k ∈ Finset.range (s + 1), if wordWeight p J.val = k then f J else 0) = f J
  simp only [Finset.sum_ite_eq, Finset.mem_range]
  exact ite_eq_left (Nat.lt_succ_of_le (boundedWord_weight J))

end RothschildStein.G3
