-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.Leibniz
public import RothschildStein.S.ClassicalWords

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology
namespace RothschildStein.S
variable {n m : ℕ}

/-- Complementary ordered subwords, retaining multiplicities
(BB p. 73). -/
def leibnizSplits : List (Fin m) → List (List (Fin m) × List (Fin m))
  | [] => [([], [])]
  | i :: I => (leibnizSplits I).map (fun p => (i :: p.1, p.2)) ++
      (leibnizSplits I).map (fun p => (p.1, i :: p.2))

/-- Both components of a complementary split are subwords (BB p. 73). -/
theorem leibnizSplits_sublist (I : List (Fin m))
    (p : List (Fin m) × List (Fin m)) (hp : p ∈ leibnizSplits I) :
    List.Sublist p.1 I ∧ List.Sublist p.2 I := by
  induction I generalizing p with
  | nil =>
    simp only [leibnizSplits, List.mem_singleton] at hp
    subst p
    simp
  | cons i I ih =>
    simp only [leibnizSplits, List.mem_append, List.mem_map] at hp
    rcases hp with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · exact ⟨(ih q hq).1.cons_cons i, (ih q hq).2.cons i⟩
    · exact ⟨(ih q hq).1.cons i, (ih q hq).2.cons_cons i⟩

/-- A word of length l has exactly 2^l Leibniz terms (BB p. 73). -/
theorem leibnizSplits_length (I : List (Fin m)) :
    (leibnizSplits I).length = 2 ^ I.length := by
  induction I with
  | nil => simp [leibnizSplits]
  | cons i I ih => simp [leibnizSplits, ih, pow_succ]; omega

/-- The sum of products over complementary subwords (BB p. 73). -/
def leibnizWordValue
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (I : List (Fin m)) (F : List (Fin m) → (Fin n → ℝ) → ℝ)
    (a : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  ((leibnizSplits I).map (fun p => F p.1 x * wordDerivative X p.2 a x)).sum

/-- Arbitrary weak word Leibniz formula with all subword derivatives
(BB p. 73). The empty representative is normalized to f. -/
theorem hasWeakWordDeriv_mul_word
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (Ω : Opens (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (I : List (Fin m)) (f a : (Fin n → ℝ) → ℝ)
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) a (Ω : Set (Fin n → ℝ)))
    (F : List (Fin m) → (Fin n → ℝ) → ℝ) (hF0 : F [] = f)
    (hF : ∀ J, List.Sublist J I → hasWeakWordDeriv X Ω J f (F J)) :
    hasWeakWordDeriv X Ω I (fun x => f x * a x) (leibnizWordValue X I F a) := by
  induction I with
  | nil =>
    have hf := (hF [] (List.Sublist.refl [])).1
    have he : leibnizWordValue X [] F a = fun x => f x * a x := by
      funext x
      simp [leibnizWordValue, leibnizSplits, wordDerivative, hF0]
    rw [he]
    exact hasWeakWordDeriv_nil X Ω (hf.mul_continuousOn ha.continuousOn Ω.isOpen.isLocallyClosed)
  | cons i I ih =>
    have hFI : ∀ J, List.Sublist J I → hasWeakWordDeriv X Ω J f (F J) :=
      fun J hJ => hF J (hJ.cons i)
    have htail := ih hFI
    apply (hasWeakWordDeriv_cons_iff X Ω hX htail i).mpr
    let l := leibnizSplits I
    have hterm : ∀ p ∈ l,
        hasWeakWordDeriv X Ω [i]
          (fun x => F p.1 x * wordDerivative X p.2 a x)
          (fun x => F (i :: p.1) x * wordDerivative X p.2 a x +
            F p.1 x * wordDerivative X (i :: p.2) a x) := by
      intro p hp
      have hs := leibnizSplits_sublist I p hp
      have hj := (hasWeakWordDeriv_cons_iff X Ω hX (hFI p.1 hs.1) i).mp
        (hF (i :: p.1) (hs.1.cons_cons i))
      exact hasWeakWordDeriv_mul_one X Ω hX i _ _ _
        (contDiffOn_wordDerivative Ω X hX p.2 a ha) hj
    have hsum := hasWeakWordDeriv_list_sum X Ω hX [i] l _ _ hterm
    convert hsum using 1
    · rfl
    · funext x
      simp only [leibnizWordValue, leibnizSplits, List.map_append, List.sum_append,
        List.map_map]
      rw [← List.sum_map_add]
      rfl

end RothschildStein.S
