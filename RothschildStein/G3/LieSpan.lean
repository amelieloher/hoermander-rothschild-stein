-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.LieWords
public import RothschildStein.G3.FilteredOperations
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- The fixed formal span viewed inside the associative finite algebra
(BB Definition 10.45, p. 525). -/
def finiteLieSpan (a s : ℕ) (p : Fin a → ℕ+) : Submodule ℝ (FiniteWordAlgebra a s p) :=
  formalSpan a s p

/-- Every nested word belongs to the finite Lie span; words beyond the
weighted cutoff vanish (BB pp. 524–525). -/
theorem nested_mem_finiteLieSpan {a s : ℕ} {p : Fin a → ℕ+} (u : Nested (Fin a)) :
    u.eval (finiteLetter (s := s) (p := p)) ∈ finiteLieSpan a s p := by
  rw [nested_eval_truncatedBracket]
  change truncatedBracket u.letters ∈ formalSpan a s p
  by_cases h : wordWeight p u.letters ≤ s
  · exact truncatedBracket_mem_span u.letters u.letters_ne_nil h
  · rw [truncatedBracket_eq_zero_of_weight_gt u.letters (by omega)]
    exact Submodule.zero_mem _

/-- Integer combinations of normalized words stay in the finite Lie span
(BB pp. 524–525). -/
theorem evaluateCombination_mem_finiteLieSpan {a s : ℕ} {p : Fin a → ℕ+}
    (c : List (ℤ × Nested (Fin a))) :
    evaluateCombination (finiteLetter (s := s) (p := p)) c ∈ finiteLieSpan a s p := by
  induction c with
  | nil => exact Submodule.zero_mem _
  | cons z c ih =>
    change z.1 • z.2.eval finiteLetter + evaluateCombination finiteLetter c ∈ _
    apply Submodule.add_mem _ _ ih
    exact zsmul_mem (nested_mem_finiteLieSpan z.2) z.1

/-- Brackets of nested words remain in the finite Lie span
(BB Lemma 1.21, p. 12; Proposition 10.44, p. 525). -/
theorem nested_bracket_mem_finiteLieSpan {a s : ℕ} {p : Fin a → ℕ+}
    (u v : Nested (Fin a)) :
    ⁅u.eval (finiteLetter (s := s) (p := p)), v.eval finiteLetter⁆ ∈ finiteLieSpan a s p := by
  rw [← normalizeBracket_eval]
  exact evaluateCombination_mem_finiteLieSpan _

/-- The fixed right-nested span is closed under the associative commutator
(BB Proposition 10.44, pp. 524–525). -/
theorem finiteLieSpan_lie_mem {a s : ℕ} {p : Fin a → ℕ+}
    {f g : FiniteWordAlgebra a s p} (hf : f ∈ finiteLieSpan a s p)
    (hg : g ∈ finiteLieSpan a s p) : ⁅f, g⁆ ∈ finiteLieSpan a s p := by
  change f ∈ Submodule.span ℝ {f : FiniteWordAlgebra a s p |
    ∃ I, I ≠ [] ∧ wordWeight p I ≤ s ∧ f = finiteBracketWord I} at hf
  change g ∈ Submodule.span ℝ {f : FiniteWordAlgebra a s p |
    ∃ I, I ≠ [] ∧ wordWeight p I ≤ s ∧ f = finiteBracketWord I} at hg
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨I, hI, _, rfl⟩ := hf
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨J, hJ, _, rfl⟩ := hg
      obtain ⟨u, hu⟩ := exists_nested_of_list I hI
      obtain ⟨v, hv⟩ := exists_nested_of_list J hJ
      have h := nested_bracket_mem_finiteLieSpan (s := s) (p := p) u v
      simpa only [nested_eval_truncatedBracket, hu, hv, finiteBracketWord] using h
    | zero => simpa only [lie_zero] using (finiteLieSpan a s p).zero_mem
    | add g h _ _ hg hh => rw [lie_add]; exact Submodule.add_mem _ hg hh
    | smul r g _ hg => rw [lie_smul]; exact Submodule.smul_mem _ r hg
  | zero => simpa only [zero_lie] using (finiteLieSpan a s p).zero_mem
  | add f h _ _ hf hh => rw [add_lie]; exact Submodule.add_mem _ hf hh
  | smul r f _ hf => rw [smul_lie]; exact Submodule.smul_mem _ r hf

/-- The concrete finite weighted coefficient Lie algebra (BB Definition 10.45,
p. 525). Its carrier remains the fixed formal span. -/
def coefficientLieAlgebra (a s : ℕ) (p : Fin a → ℕ+) :
    LieSubalgebra ℝ (FiniteWordAlgebra a s p) where
  __ := finiteLieSpan a s p
  lie_mem' := finiteLieSpan_lie_mem

end RothschildStein.G3
