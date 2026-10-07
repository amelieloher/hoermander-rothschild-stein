-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.Commutation
public import Mathlib.Data.Set.Finite.List

/-!
# No-drift commutation of word derivatives with endpoint operators

Without drift, all weights are one. The no-drift commutation formula
`noDrift_commutation_of_transfer` gives, for a type-`1` operator `C` and generator `i`,
`X̃ᵢ C = ∑ⱼ C_{ij} X̃ⱼ + C_{i0}` on tests, with `C_{ij}` and `C_{i0}` also of type `1`.
Iterating, the weak derivative `X̃_I (C f)` of a type-`1` image of a test is a finite sum
`∑_a C_a (X̃_{J_a} f)` with type-`1` operators `C_a` and words `|J_a| ≤ |I|` (BB p. 567,
proof of Prop. 11.31).

A *type-1 form* is a finite list of pairs `(J, C)` ("`C` applied to `X̃_J f`"), evaluated by
`formApply`. One step of commutation (`exists_form_step`) maps a form of word length at most `m`
to a form of word length at most `m + 1` with the same weak `X̃ᵢ`-derivative; iterating over a word
(`exists_form_word`) raises the word length by the length of the word. Finally a form is collected
by words (`exists_collected_form`): one type-1 operator `C_J` for each word `J` of length at most
`n` (finite index set `wordsUpTo k n`).

All statements assume the type-calculus hypotheses used by the commutation formula: row
integrability (`TypeKernelIntegrable`), right differentiation (`RightDifferentiation`) and transfer to the
integration variable (`DerivativeTransfer`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped Topology
namespace RothschildStein.P1

variable {N k : ℕ} {F : KernelFrame N} {w : Fin k → ℕ+}
  {Xt : Fin k → (Fin N → ℝ) → (Fin N → ℝ)}

/-- The finite set of words over `Fin k` of length at most `n` (the index set of the
commuted families through level `n`). -/
def wordsUpTo (k n : ℕ) : Finset (List (Fin k)) := (List.finite_length_le (Fin k) n).toFinset

/-- Membership in the words of length at most `n`. -/
theorem mem_wordsUpTo {n : ℕ} {J : List (Fin k)} : J ∈ wordsUpTo k n ↔ J.length ≤ n := by
  simp [wordsUpTo]

/-- The only word of length at most zero is the empty word. -/
theorem wordsUpTo_zero : wordsUpTo k 0 = {[]} := by
  ext J
  simp [mem_wordsUpTo]

/-- A term of a type-1 form: a word `J` and a type-1 operator `C`, standing for the
functional `f ↦ C (X̃_J f)`. -/
abbrev TypeOneTerm (F : KernelFrame N) (k : ℕ) : Type := List (Fin k) × TypeOperator F 1

/-- The type-1 form `f ↦ ∑_a C_a (X̃_{J_a} f)` of a finite list of terms (duplicated words
are kept). -/
def formApply (Xt : Fin k → (Fin N → ℝ) → (Fin N → ℝ)) (L : List (TypeOneTerm F k))
    (f : TestFunction F.V ℝ (⊤ : ℕ∞)) (ξ : Fin N → ℝ) : ℝ :=
  (L.map fun p => p.2.apply (wordDerivative Xt p.1 (f : (Fin N → ℝ) → ℝ)) ξ).sum

/-- The empty form is zero. -/
theorem formApply_nil (f : TestFunction F.V ℝ (⊤ : ℕ∞)) :
    formApply Xt ([] : List (TypeOneTerm F k)) f = fun _ => 0 := by
  funext ξ
  simp [formApply]

/-- A form splits into its first term and the rest. -/
theorem formApply_cons (p : TypeOneTerm F k) (L : List (TypeOneTerm F k))
    (f : TestFunction F.V ℝ (⊤ : ℕ∞)) (ξ : Fin N → ℝ) :
    formApply Xt (p :: L) f ξ =
      p.2.apply (wordDerivative Xt p.1 (f : (Fin N → ℝ) → ℝ)) ξ + formApply Xt L f ξ := by
  simp [formApply]

/-- Forms of concatenated lists add. -/
theorem formApply_append (L₁ L₂ : List (TypeOneTerm F k)) (f : TestFunction F.V ℝ (⊤ : ℕ∞))
    (ξ : Fin N → ℝ) :
    formApply Xt (L₁ ++ L₂) f ξ = formApply Xt L₁ f ξ + formApply Xt L₂ f ξ := by
  simp [formApply, List.sum_append]

/-- Weak derivatives of finite sums add (finite-set version of
`S.hasWeakWordDeriv_list_sum`). -/
theorem hasWeakWordDeriv_finset_sum {ι : Type*}
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (F.V : Set (Fin N → ℝ)))
    (I : List (Fin k)) (s : Finset ι) (f g : ι → (Fin N → ℝ) → ℝ)
    (h : ∀ a ∈ s, hasWeakWordDeriv Xt F.V I (f a) (g a)) :
    hasWeakWordDeriv Xt F.V I (fun x => ∑ a ∈ s, f a x) (fun x => ∑ a ∈ s, g a x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using S.hasWeakWordDeriv_zero Xt F.V I
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact S.hasWeakWordDeriv_add Xt F.V hXt (h a (Finset.mem_insert_self a s))
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

section Hypotheses

variable (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (F.V : Set (Fin N → ℝ)))
  (hw : ∀ j, (w j : ℕ) = 1) (B : Fin N → List (Fin k))
  (hRowInt : TypeKernelIntegrable F) (hRightDiff : RightDifferentiation F w Xt hXt) (hTransfer : DerivativeTransfer F w Xt B)
include hXt hw hRowInt hRightDiff hTransfer

/-- The weak `X̃ᵢ`-derivative of a type-1 image of a test exists and is a type-1 combination
(the commutation formula without drift, with `lam = 1`): a *provider* of weak derivatives for `hasWeakWordDeriv_formApply`.
For every type-1 `C` and generator `i` there is a function `r` with `r g` the weak `X̃ᵢ`-derivative
of `C g` for every test `g`. -/
theorem exists_weakDeriv_typeOne (C : TypeOperator F 1) (i : Fin k) :
    ∃ r : TestFunction F.V ℝ (⊤ : ℕ∞) → (Fin N → ℝ) → ℝ,
      ∀ g : TestFunction F.V ℝ (⊤ : ℕ∞),
        hasWeakWordDeriv Xt F.V [i] (C.apply (g : (Fin N → ℝ) → ℝ)) (r g) := by
  obtain ⟨Fh, F0, h⟩ := noDrift_commutation_of_transfer hXt hw B hRowInt hRightDiff hTransfer le_rfl C i
  exact ⟨fun g ξ => (∑ j, (Fh j).apply (fieldDerivative (Xt j) (g : (Fin N → ℝ) → ℝ)) ξ) +
    F0.apply (g : (Fin N → ℝ) → ℝ) ξ, h⟩

/-- One step of commutation: a type-1 form with words of length at most `m` has a weak
`X̃ᵢ`-derivative equal to a type-1 form with words of length at most `m + 1`. Each term
`C (X̃_J f)` contributes `∑ⱼ C_{ij} (X̃ⱼ X̃_J f) + C_{i0} (X̃_J f)` (the commutation formula). -/
theorem exists_form_step (i : Fin k) :
    ∀ (L : List (TypeOneTerm F k)) (m : ℕ), (∀ p ∈ L, p.1.length ≤ m) →
      ∃ L' : List (TypeOneTerm F k), (∀ p ∈ L', p.1.length ≤ m + 1) ∧
        ∀ f : TestFunction F.V ℝ (⊤ : ℕ∞),
          hasWeakWordDeriv Xt F.V [i] (formApply Xt L f) (formApply Xt L' f) := by
  intro L m
  induction L with
  | nil =>
    intro _
    refine ⟨[], by simp, fun f => ?_⟩
    rw [formApply_nil]
    exact S.hasWeakWordDeriv_zero Xt F.V [i]
  | cons p L ih =>
    intro hL
    obtain ⟨L', hL', hweak⟩ := ih fun q hq => hL q (List.mem_cons_of_mem p hq)
    obtain ⟨Fh, F0, hFh⟩ := noDrift_commutation_of_transfer hXt hw B hRowInt hRightDiff hTransfer le_rfl p.2 i
    have hp : p.1.length ≤ m := hL p List.mem_cons_self
    refine ⟨((List.finRange k).map fun j => (j :: p.1, Fh j)) ++ (p.1, F0) :: L', ?_, fun f => ?_⟩
    · intro q hq
      rcases List.mem_append.1 hq with hq | hq
      · obtain ⟨j, -, rfl⟩ := List.mem_map.1 hq
        simp only [List.length_cons]
        omega
      · rcases List.mem_cons.1 hq with rfl | hq
        · exact hp.trans (Nat.le_succ m)
        · exact hL' q hq
    · have h := S.hasWeakWordDeriv_add Xt F.V hXt (hFh (S.wordDerivativeTest F.V Xt hXt p.1 f))
        (hweak f)
      have e1 : formApply Xt (p :: L) f = fun ξ =>
          p.2.apply (wordDerivative Xt p.1 (f : (Fin N → ℝ) → ℝ)) ξ + formApply Xt L f ξ :=
        funext fun ξ => formApply_cons p L f ξ
      have e2 : formApply Xt (((List.finRange k).map fun j => (j :: p.1, Fh j)) ++
          (p.1, F0) :: L') f = fun ξ =>
          ((∑ j, (Fh j).apply (fieldDerivative (Xt j)
              (wordDerivative Xt p.1 (f : (Fin N → ℝ) → ℝ))) ξ) +
            F0.apply (wordDerivative Xt p.1 (f : (Fin N → ℝ) → ℝ)) ξ) +
          formApply Xt L' f ξ := by
        funext ξ
        rw [formApply_append, formApply_cons, formApply]
        simp only [List.map_map, Function.comp_def, wordDerivative, Fin.sum_univ_def]
        ring
      rw [e1, e2]
      exact h

/-- Iterated commutation along a nonempty word `i :: I` (that is, `X̃ᵢ X̃_I`): a type-1 form
with words of length at most `m` has a weak `X̃_{i :: I}`-derivative equal to a type-1 form with
words of length at most `m + |i :: I|`. -/
theorem exists_form_word (m : ℕ) (L : List (TypeOneTerm F k)) (hL : ∀ p ∈ L, p.1.length ≤ m) :
    ∀ (I : List (Fin k)) (i : Fin k), ∃ L' : List (TypeOneTerm F k),
      (∀ p ∈ L', p.1.length ≤ m + (i :: I).length) ∧
        ∀ f : TestFunction F.V ℝ (⊤ : ℕ∞),
          hasWeakWordDeriv Xt F.V (i :: I) (formApply Xt L f) (formApply Xt L' f) := by
  intro I
  induction I with
  | nil =>
    intro i
    obtain ⟨L', hL', h⟩ := exists_form_step hXt hw B hRowInt hRightDiff hTransfer i L m hL
    exact ⟨L', by simpa using hL', h⟩
  | cons a I ih =>
    intro i
    obtain ⟨L₁, h₁, hw₁⟩ := ih a
    obtain ⟨L₂, h₂, hw₂⟩ := exists_form_step hXt hw B hRowInt hRightDiff hTransfer i L₁ _ h₁
    refine ⟨L₂, fun p hp => ?_, fun f => ?_⟩
    · have := h₂ p hp
      simp only [List.length_cons] at this ⊢
      omega
    · exact (S.hasWeakWordDeriv_cons_iff Xt F.V hXt (hw₁ f) i).2 (hw₂ f)

end Hypotheses

/-- Collecting a type-1 form by words: a form whose words have length at most `n` is
`∑_{|J| ≤ n} C_J (X̃_J f)` with one type-1 operator `C_J` for each word (operators with the same
word add, by linearity of positive-type operators on test inputs). -/
theorem exists_collected_form
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (F.V : Set (Fin N → ℝ)))
    (hRowInt : TypeKernelIntegrable F) (n : ℕ) (L : List (TypeOneTerm F k))
    (hL : ∀ p ∈ L, p.1.length ≤ n) :
    ∃ C : List (Fin k) → TypeOperator F 1, ∀ (f : TestFunction F.V ℝ (⊤ : ℕ∞)) (ξ : Fin N → ℝ),
      formApply Xt L f ξ =
        ∑ J ∈ wordsUpTo k n, (C J).apply (wordDerivative Xt J (f : (Fin N → ℝ) → ℝ)) ξ := by
  classical
  induction L with
  | nil =>
    exact ⟨fun _ => TypeOperator.zero F 1, fun f ξ => by
      simp [formApply, TypeOperator.apply_zero one_ne_zero]⟩
  | cons p L ih =>
    obtain ⟨C, hC⟩ := ih fun q hq => hL q (List.mem_cons_of_mem p hq)
    refine ⟨fun J => if J = p.1 then p.2.add (C J) else C J, fun f ξ => ?_⟩
    have hp : p.1 ∈ wordsUpTo k n := mem_wordsUpTo.2 (hL p List.mem_cons_self)
    have key : ∀ J : List (Fin k),
        ((if J = p.1 then p.2.add (C J) else C J : TypeOperator F 1).apply
          (wordDerivative Xt J (f : (Fin N → ℝ) → ℝ)) ξ) =
        (if J = p.1 then p.2.apply (wordDerivative Xt p.1 (f : (Fin N → ℝ) → ℝ)) ξ else 0) +
          (C J).apply (wordDerivative Xt J (f : (Fin N → ℝ) → ℝ)) ξ := by
      intro J
      by_cases hJ : J = p.1
      · rw [hJ]
        simp only [ite_true]
        exact TypeOperator.apply_add hRowInt one_ne_zero p.2 (C p.1)
          (isTestInput_wordDerivative hXt p.1 f) ξ
      · simp [hJ]
    rw [formApply_cons, hC f ξ]
    simp_rw [key]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq' (wordsUpTo k n) p.1]
    simp [hp]

end RothschildStein.P1
