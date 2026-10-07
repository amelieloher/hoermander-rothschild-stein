-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.TypeClosure
public import RothschildStein.P1.BracketExpansion

/-!
# Right composition by words and right forms

Two ingredients of the proof of the commutation formula (BB pp. 559–560, Thm 11.19):

* `exists_rightWord`: iterating right differentiation (`RightDifferentiation`), a type-`t` operator
  composed on the right with a word of weight `|σ| ≤ t` is a type-`(t - |σ|)` operator, on tests.
  Each intermediate composition is permitted since the remaining type exceeds the weight still to
  be composed.
* `RightForm F w Xt t Ψ`: the functional `f ↦ Ψ f` on tests has the shape
  `Ψ f = ∑_r C_r X̃_r f` with `C_r` of type `t + w r`. The class contains right-composed operators
  and is closed under finite signed sums (`zero`, `add`, `smul`, `listSum`, `sum`); this is the
  bookkeeping that collects the words of a bracket expansion by their rightmost letter.
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

/-- The weight of a concatenation. -/
theorem wordWeight_append (w : Fin k → ℕ+) (σ τ : List (Fin k)) :
    wordWeight w (σ ++ τ) = wordWeight w σ + wordWeight w τ := by
  simp [wordWeight]

/-- The weight of a one-letter word. -/
theorem wordWeight_singleton (w : Fin k → ℕ+) (a : Fin k) : wordWeight w [a] = (w a : ℕ) := by
  simp [wordWeight]

/-- The weight of a cons. -/
theorem wordWeight_cons (w : Fin k → ℕ+) (a : Fin k) (σ : List (Fin k)) :
    wordWeight w (a :: σ) = (w a : ℕ) + wordWeight w σ := by
  simp [wordWeight]

/-- Word derivatives of a test function are test inputs. -/
theorem isTestInput_wordDerivative
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (F.V : Set (Fin N → ℝ))) (σ : List (Fin k))
    (f : TestFunction F.V ℝ (⊤ : ℕ∞)) :
    IsTestInput (wordDerivative Xt σ (f : (Fin N → ℝ) → ℝ)) :=
  IsTestInput.of_testFunction (S.wordDerivativeTest F.V Xt hXt σ f)

/-- A field derivative of a test function is a test input. -/
theorem isTestInput_fieldDerivative
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (F.V : Set (Fin N → ℝ))) (r : Fin k)
    (f : TestFunction F.V ℝ (⊤ : ℕ∞)) :
    IsTestInput (fieldDerivative (Xt r) (f : (Fin N → ℝ) → ℝ)) :=
  isTestInput_wordDerivative hXt [r] f

/-- Right composition by a word (iterated right differentiation, BB p. 551 and pp. 559–560): composing a
type-`t` operator on the right with the word `σ` of weight at most `t` gives a type-`(t - |σ|)`
operator, on every test function. -/
theorem exists_rightWord
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (F.V : Set (Fin N → ℝ)))
    (hRightDiff : RightDifferentiation F w Xt hXt) (σ : List (Fin k)) :
    ∀ (t : ℕ) (T : TypeOperator F t), wordWeight w σ ≤ t →
      ∃ R : TypeOperator F (t - wordWeight w σ), ∀ g : TestFunction F.V ℝ (⊤ : ℕ∞),
        T.apply (S.wordDerivativeTest F.V Xt hXt σ g) = R.apply g := by
  induction σ with
  | nil =>
    intro t T _
    refine ⟨T.ofEq (by simp [wordWeight]), fun g => ?_⟩
    ext ξ
    rw [TypeOperator.apply_ofEq]
    rfl
  | cons a σ ih =>
    intro t T hT
    rw [wordWeight_cons] at hT
    obtain ⟨R₁, hR₁⟩ := hRightDiff t T a (by omega)
    obtain ⟨R₂, hR₂⟩ := ih (t - w a) R₁ (by omega)
    refine ⟨R₂.ofEq (by rw [wordWeight_cons]; omega), fun g => ?_⟩
    ext ξ
    rw [TypeOperator.apply_ofEq, ← hR₂]
    exact congrFun (hR₁ (S.wordDerivativeTest F.V Xt hXt σ g)) ξ

/-- The functional `f ↦ Ψ f` on tests is a *right form of base type `t`*: it is
`∑_r C_r X̃_r f` with `C_r` a type-`(t + w r)` operator (collection of the words of a bracket
expansion by their rightmost letter, as in the proof of the commutation formula). -/
def RightForm (F : KernelFrame N) (w : Fin k → ℕ+) (Xt : Fin k → (Fin N → ℝ) → (Fin N → ℝ))
    (t : ℕ) (Ψ : TestFunction F.V ℝ (⊤ : ℕ∞) → (Fin N → ℝ) → ℝ) : Prop :=
  ∃ C : ∀ r : Fin k, TypeOperator F (t + (w r : ℕ)),
    ∀ (f : TestFunction F.V ℝ (⊤ : ℕ∞)) (ξ : Fin N → ℝ),
      Ψ f ξ = ∑ r, (C r).apply (fieldDerivative (Xt r) (f : (Fin N → ℝ) → ℝ)) ξ

/-- Types `t + w r` are positive, since weights are positive. -/
theorem add_weight_ne_zero (w : Fin k → ℕ+) (t : ℕ) (r : Fin k) : t + (w r : ℕ) ≠ 0 := by
  have := (w r).pos
  omega

namespace RightForm

variable {t : ℕ} {Ψ Ψ' : TestFunction F.V ℝ (⊤ : ℕ∞) → (Fin N → ℝ) → ℝ}

/-- Equal functionals have equal right forms. -/
theorem congr (h : ∀ f ξ, Ψ f ξ = Ψ' f ξ) (hΨ' : RightForm F w Xt t Ψ') :
    RightForm F w Xt t Ψ := by
  obtain ⟨C, hC⟩ := hΨ'
  exact ⟨C, fun f ξ => (h f ξ).trans (hC f ξ)⟩

/-- The zero functional is a right form of every base type. -/
theorem zero : RightForm F w Xt t (fun _ _ => 0) :=
  ⟨fun r => TypeOperator.zero F _, fun f ξ => by
    simp [TypeOperator.apply_zero (add_weight_ne_zero w t _)]⟩

/-- Right forms are closed under sums. -/
theorem add (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (F.V : Set (Fin N → ℝ)))
    (hRowInt : TypeKernelIntegrable F) (h₁ : RightForm F w Xt t Ψ) (h₂ : RightForm F w Xt t Ψ') :
    RightForm F w Xt t (fun f ξ => Ψ f ξ + Ψ' f ξ) := by
  obtain ⟨C₁, hC₁⟩ := h₁
  obtain ⟨C₂, hC₂⟩ := h₂
  refine ⟨fun r => (C₁ r).add (C₂ r), fun f ξ => ?_⟩
  show Ψ f ξ + Ψ' f ξ = _
  rw [hC₁, hC₂, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [TypeOperator.apply_add hRowInt (add_weight_ne_zero w t r) _ _
    (isTestInput_fieldDerivative hXt r f)]

/-- Right forms are closed under real multiples. -/
theorem smul (c : ℝ) (h : RightForm F w Xt t Ψ) :
    RightForm F w Xt t (fun f ξ => c * Ψ f ξ) := by
  obtain ⟨C, hC⟩ := h
  refine ⟨fun r => (C r).smul c, fun f ξ => ?_⟩
  show c * Ψ f ξ = _
  rw [hC, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [TypeOperator.apply_smul (add_weight_ne_zero w t r)]

/-- A single right-composed operator `f ↦ R (X̃_r f)` with `R` of type `t + w r` is a right
form. -/
theorem single (r : Fin k) (R : TypeOperator F (t + (w r : ℕ))) :
    RightForm F w Xt t (fun f ξ => R.apply (fieldDerivative (Xt r) (f : (Fin N → ℝ) → ℝ)) ξ) := by
  classical
  refine ⟨fun r' => if h : r' = r then
    R.ofEq (by rw [h]) else TypeOperator.zero F _, fun f ξ => ?_⟩
  rw [Finset.sum_eq_single r]
  · simp [TypeOperator.apply_ofEq]
  · intro r' _ hr'
    simp [hr', TypeOperator.apply_zero (add_weight_ne_zero w t r')]
  · intro h
    exact absurd (Finset.mem_univ r) h

/-- Right forms are closed under signed list sums. -/
theorem listSum (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (F.V : Set (Fin N → ℝ)))
    (hRowInt : TypeKernelIntegrable F) {ι : Type*} (l : List ι) (c : ι → ℝ)
    {Φ : ι → TestFunction F.V ℝ (⊤ : ℕ∞) → (Fin N → ℝ) → ℝ}
    (h : ∀ a ∈ l, RightForm F w Xt t (Φ a)) :
    RightForm F w Xt t (fun f ξ => (l.map fun a => c a * Φ a f ξ).sum) := by
  induction l with
  | nil => simpa using (zero : RightForm F w Xt t (fun _ _ => 0))
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact ((h a List.mem_cons_self).smul (c a)).add hXt hRowInt
      (ih fun b hb => h b (List.mem_cons_of_mem a hb))

/-- Right forms are closed under finite sums. -/
theorem sum (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (F.V : Set (Fin N → ℝ)))
    (hRowInt : TypeKernelIntegrable F) {ι : Type*} (s : Finset ι)
    {Φ : ι → TestFunction F.V ℝ (⊤ : ℕ∞) → (Fin N → ℝ) → ℝ}
    (h : ∀ a ∈ s, RightForm F w Xt t (Φ a)) :
    RightForm F w Xt t (fun f ξ => ∑ a ∈ s, Φ a f ξ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero : RightForm F w Xt t (fun _ _ => 0))
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add hXt hRowInt
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

/-- A word derivative of a nonempty word applied to a test, against a type-`(t + |σ|)`
operator, is a right form of base type `t`: the rightmost letter `r` of `σ` is split off and the
prefix is composed on the right by `exists_rightWord`, leaving type `t + |σ| - |σ'| = t + w r`
(BB p. 559, "if a word's rightmost generator is horizontal, compose its prefix of weight
`|J| - 1`"; drift: prefix of weight `|J| - 2`). -/
theorem of_word (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (F.V : Set (Fin N → ℝ)))
    (hRightDiff : RightDifferentiation F w Xt hXt) {t t' : ℕ} (σ : List (Fin k)) (hσ : σ ≠ [])
    (ht : t' = t + wordWeight w σ) (T : TypeOperator F t') :
    RightForm F w Xt t
      (fun f ξ => T.apply (wordDerivative Xt σ (f : (Fin N → ℝ) → ℝ)) ξ) := by
  obtain ⟨σ', r, rfl⟩ : ∃ (σ' : List (Fin k)) (r : Fin k), σ = σ' ++ [r] := by
    exact (List.eq_nil_or_concat' σ).resolve_left hσ
  have hw : wordWeight w (σ' ++ [r]) = wordWeight w σ' + (w r : ℕ) := by
    rw [wordWeight_append, wordWeight_singleton]
  obtain ⟨R, hR⟩ := exists_rightWord hXt hRightDiff σ' t' T (by omega)
  refine RightForm.congr (fun f ξ => ?_) (single (t := t) r (R.ofEq (by omega)))
  rw [TypeOperator.apply_ofEq, wordDerivative_append]
  exact congrFun (hR (S.wordDerivativeTest F.V Xt hXt [r] f)) ξ

end RightForm

/-! ### Selecting the operators of a given weight -/

/-- Selection of a letter's operator by its weight: the operator `T` of type
`t + w r` as an operator of type `t + c` when `w r = c`, and zero otherwise. -/
def TypeOperator.ofWeight (w : Fin k → ℕ+) {t : ℕ} {r : Fin k} (c : ℕ)
    (T : TypeOperator F (t + (w r : ℕ))) : TypeOperator F (t + c) :=
  if h : (w r : ℕ) = c then T.ofEq (by rw [h]) else TypeOperator.zero F _

/-- The selected operator acts as the original one when the weight matches. -/
theorem TypeOperator.apply_ofWeight (w : Fin k → ℕ+) {t : ℕ} {r : Fin k} (c : ℕ)
    (T : TypeOperator F (t + (w r : ℕ))) (h : (w r : ℕ) = c) (g : (Fin N → ℝ) → ℝ)
    (ξ : Fin N → ℝ) : (TypeOperator.ofWeight w c T).apply g ξ = T.apply g ξ := by
  simp [TypeOperator.ofWeight, h, TypeOperator.apply_ofEq]

/-- A sum over all letters of weights one or two splits by weight. -/
theorem sum_split_weights (hw : ∀ j, (w j : ℕ) = 1 ∨ (w j : ℕ) = 2) (g : Fin k → ℝ) :
    ∑ j, g j = (∑ j ∈ Finset.univ.filter (fun j => (w j : ℕ) = 1), g j) +
      ∑ j ∈ Finset.univ.filter (fun j => (w j : ℕ) = 2), g j := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => (w j : ℕ) = 1)]
  congr 1
  refine Finset.sum_congr (Finset.filter_congr fun j _ => ?_) fun _ _ => rfl
  rcases hw j with h | h <;> simp [h]

end RothschildStein.P1
