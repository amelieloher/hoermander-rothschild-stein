-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.BracketAlgebra
public import RothschildStein.S.ClassicalWords
public import RothschildStein.S.FieldDerivativeListSum
public import RothschildStein.Definitions.wordBracket
public import RothschildStein.Definitions.wordWeight

/-!
# Bracket expansion into ordered words

For fields `X i` smooth on an open set `Ω` and a function `f` smooth on `Ω`, the derivative of `f`
along the nested bracket `[X_{i₁}, [X_{i₂}, …, X_{iₗ}]]` is a finite signed sum of ordered word
derivatives `X_{σ₁} ⋯ X_{σₗ} f`, each word `σ` being a rearrangement of the letters `i₁ … iₗ`
(so of the same weight). This is the expansion `[A, B] f = A (B f) - B (A f)` iterated along the
right-nested bracket (BB pp. 559–560, proof of Thm 11.19). The expansion is a list of
`(sign, word)` pairs in which equal words may repeat; the test-function form is an equality of
global functions, since both sides vanish off `Ω` for a test function supported in `Ω`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped Topology
namespace RothschildStein.P1

variable {n m : ℕ}

/-- The signed ordered words of the nested bracket `wordBracket X J`:
`[X_i, B] ↦ {(s, i σ)} ∪ {(-s, σ i)}` for the words `(s, σ)` of `B` (BB p. 559, bracket
`[A, B] = AB - BA`). -/
def bracketWords : List (Fin m) → List (ℤ × List (Fin m))
  | [] => []
  | [i] => [(1, [i])]
  | i :: j :: I =>
    (bracketWords (j :: I)).map (fun p => (p.1, i :: p.2)) ++
      (bracketWords (j :: I)).map (fun p => (-p.1, p.2 ++ [i]))

/-- The classical derivative `∑ ± X_σ f (x)` of `f` along a signed family of ordered
words. -/
def signedWordDerivative (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (E : List (ℤ × List (Fin m))) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  (E.map fun p => (p.1 : ℝ) * wordDerivative X p.2 f x).sum

/-- A word derivative of a concatenated word is the composite of the two. -/
theorem wordDerivative_append (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (σ τ : List (Fin m))
    (f : (Fin n → ℝ) → ℝ) :
    wordDerivative X (σ ++ τ) f = wordDerivative X σ (wordDerivative X τ f) := by
  induction σ with
  | nil => rfl
  | cons a σ ih => simp only [List.cons_append, wordDerivative, ih]

/-- The derivative along the constant-multiple of a function. -/
theorem fieldDerivative_const_mul (V : (Fin n → ℝ) → (Fin n → ℝ)) (c : ℝ)
    (g : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) (hg : DifferentiableAt ℝ g x) :
    fieldDerivative V (fun y => c * g y) x = c * fieldDerivative V g x := by
  simp only [fieldDerivative]
  rw [fderiv_const_mul hg c]
  simp

/-- A field derivative distributes over a signed list sum of differentiable terms. -/
theorem fieldDerivative_signedSum (V : (Fin n → ℝ) → (Fin n → ℝ)) {α : Type*}
    (E : List (ℤ × α)) (g : α → (Fin n → ℝ) → ℝ) (x : Fin n → ℝ)
    (hg : ∀ p ∈ E, DifferentiableAt ℝ (g p.2) x) :
    fieldDerivative V (fun y => (E.map fun p => (p.1 : ℝ) * g p.2 y).sum) x =
      (E.map fun p => (p.1 : ℝ) * fieldDerivative V (g p.2) x).sum := by
  have h := S.fieldDerivative_listSum V E (fun p y => (p.1 : ℝ) * g p.2 y) x
    (fun p hp => (hg p hp).const_mul _)
  rw [h]
  congr 1
  exact List.map_congr_left fun p hp => fieldDerivative_const_mul V _ _ x (hg p hp)

/-- Words of a nested bracket are rearrangements of its letters. -/
theorem perm_of_mem_bracketWords {J : List (Fin m)} :
    ∀ {p : ℤ × List (Fin m)}, p ∈ bracketWords J → p.2.Perm J := by
  induction J with
  | nil => intro p hp; simp [bracketWords] at hp
  | cons i J ih =>
    cases J with
    | nil =>
      intro p hp
      simp only [bracketWords, List.mem_singleton] at hp
      subst hp
      exact List.Perm.refl _
    | cons j I =>
      intro p hp
      simp only [bracketWords, List.mem_append, List.mem_map] at hp
      rcases hp with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
      · exact (ih hq).cons i
      · exact (List.perm_append_singleton i q.2).trans ((ih hq).cons i)

/-- Every word of a nested bracket has the weight of the bracket. -/
theorem wordWeight_of_mem_bracketWords {w : Fin m → ℕ+} {J : List (Fin m)}
    {p : ℤ × List (Fin m)} (hp : p ∈ bracketWords J) : wordWeight w p.2 = wordWeight w J :=
  ((perm_of_mem_bracketWords hp).map _).sum_eq

/-- A nonempty-weight bracket has only nonempty words: a word of a bracket of positive
weight is nonempty. -/
theorem ne_nil_of_mem_bracketWords {J : List (Fin m)} {p : ℤ × List (Fin m)}
    (hp : p ∈ bracketWords J) : p.2 ≠ [] := by
  intro h
  have hJ : J = [] := by
    have := perm_of_mem_bracketWords hp
    rw [h] at this
    exact (List.Perm.nil_eq this).symm
  subst hJ
  simp [bracketWords] at hp

/-- Bracket expansion (BB pp. 559–560, proof of Thm 11.19): for fields smooth on `Ω` and
`f` smooth on `Ω`, the derivative along `wordBracket X J` is the signed sum of ordered word
derivatives of `bracketWords J`, at every point of `Ω`. -/
theorem fieldDerivative_wordBracket_eq (Ω : Opens (Fin n → ℝ))
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ))) (J : List (Fin m)) :
    ∀ f : (Fin n → ℝ) → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) f (Ω : Set (Fin n → ℝ)) →
      ∀ x ∈ (Ω : Set (Fin n → ℝ)),
        fieldDerivative (wordBracket X J) f x = signedWordDerivative X (bracketWords J) f x := by
  induction J with
  | nil =>
    intro f hf x hx
    simp [wordBracket, bracketWords, signedWordDerivative, fieldDerivative]
  | cons i J ih =>
    cases J with
    | nil =>
      intro f hf x hx
      simp [wordBracket, bracketWords, signedWordDerivative, wordDerivative]
    | cons j I =>
      intro f hf x hx
      have hnhds : (Ω : Set (Fin n → ℝ)) ∈ 𝓝 x := Ω.isOpen.mem_nhds hx
      have hBd : DifferentiableAt ℝ (wordBracket X (j :: I)) x :=
        ((G1.wordBracket_contDiffOn Ω.isOpen X hX (j :: I)).contDiffAt hnhds).differentiableAt
          (by simp)
      have hAd : DifferentiableAt ℝ (X i) x :=
        ((hX i).contDiffAt hnhds).differentiableAt (by simp)
      have key := VectorField.fderiv_apply_lieBracket (𝕜 := ℝ) (n := (⊤ : ℕ∞))
        (hf.contDiffAt hnhds) (by simp) hBd hAd
      -- first term: `X_i (B f)`
      have h1 : fieldDerivative (X i) (fieldDerivative (wordBracket X (j :: I)) f) x =
          (((bracketWords (j :: I)).map (fun p => (p.1, i :: p.2))).map
            fun p => (p.1 : ℝ) * wordDerivative X p.2 f x).sum := by
        have heq : fieldDerivative (wordBracket X (j :: I)) f =ᶠ[𝓝 x]
            signedWordDerivative X (bracketWords (j :: I)) f :=
          Filter.eventuallyEq_of_mem hnhds fun y hy => ih f hf y hy
        have h' : fieldDerivative (X i) (fieldDerivative (wordBracket X (j :: I)) f) x =
            fieldDerivative (X i) (signedWordDerivative X (bracketWords (j :: I)) f) x := by
          simp only [fieldDerivative]
          rw [heq.fderiv_eq]
        rw [h']
        unfold signedWordDerivative
        rw [fieldDerivative_signedSum (X i) (bracketWords (j :: I))
          (fun σ => wordDerivative X σ f) x]
        · rw [List.map_map]
          congr 1
        · intro p _
          exact ((S.contDiffOn_wordDerivative Ω X hX p.2 f hf).contDiffAt hnhds).differentiableAt
            (by simp)
      -- second term: `B (X_i f)`
      have h2 : fieldDerivative (wordBracket X (j :: I)) (fieldDerivative (X i) f) x =
          (((bracketWords (j :: I)).map (fun p => (p.1, p.2 ++ [i]))).map
            fun p => (p.1 : ℝ) * wordDerivative X p.2 f x).sum := by
        rw [ih _ (S.contDiffOn_fieldDerivative Ω (X i) f (hX i) hf) x hx]
        unfold signedWordDerivative
        rw [List.map_map]
        congr 1
        refine List.map_congr_left fun p _ => ?_
        simp only [Function.comp, wordDerivative_append]
        rfl
      show fderiv ℝ f x (VectorField.lieBracket ℝ (X i) (wordBracket X (j :: I)) x) = _
      rw [key]
      change fieldDerivative (X i) (fieldDerivative (wordBracket X (j :: I)) f) x -
        fieldDerivative (wordBracket X (j :: I)) (fieldDerivative (X i) f) x = _
      rw [h1, h2]
      have hneg : ∀ E : List (ℤ × List (Fin m)),
          (E.map ((fun p : ℤ × List (Fin m) => (p.1 : ℝ) * wordDerivative X p.2 f x) ∘
            fun p => (-p.1, p.2 ++ [i]))).sum =
          -(E.map ((fun p : ℤ × List (Fin m) => (p.1 : ℝ) * wordDerivative X p.2 f x) ∘
            fun p => (p.1, p.2 ++ [i]))).sum := by
        intro E
        induction E with
        | nil => simp
        | cons a E ih =>
          simp only [List.map_cons, List.sum_cons, ih, Function.comp, Int.cast_neg, neg_mul]
          ring
      unfold signedWordDerivative
      simp only [bracketWords, List.map_append, List.sum_append, List.map_map]
      rw [hneg]
      ring

/-- Bracket expansion for a test function: the equality holds as global functions, because
a test function supported in `Ω` has all its word derivatives supported in `Ω`. -/
theorem fieldDerivative_wordBracket_test (Ω : Opens (Fin n → ℝ))
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ))) (J : List (Fin m))
    (φ : TestFunction Ω ℝ (⊤ : ℕ∞)) :
    fieldDerivative (wordBracket X J) (φ : (Fin n → ℝ) → ℝ) =
      signedWordDerivative X (bracketWords J) (φ : (Fin n → ℝ) → ℝ) := by
  funext x
  by_cases hx : x ∈ (Ω : Set (Fin n → ℝ))
  · exact fieldDerivative_wordBracket_eq Ω X hX J φ φ.contDiff.contDiffOn x hx
  · have hxφ : x ∉ tsupport (φ : (Fin n → ℝ) → ℝ) := fun h => hx (φ.tsupport_subset h)
    have h0 : fieldDerivative (wordBracket X J) (φ : (Fin n → ℝ) → ℝ) x = 0 :=
      image_eq_zero_of_notMem_tsupport fun h => hxφ (S.tsupport_fieldDerivative_subset _ _ h)
    rw [h0]
    unfold signedWordDerivative
    symm
    apply List.sum_eq_zero
    intro a ha
    obtain ⟨p, _, rfl⟩ := List.mem_map.1 ha
    have : wordDerivative X p.2 (φ : (Fin n → ℝ) → ℝ) x = 0 :=
      image_eq_zero_of_notMem_tsupport fun h => hxφ (S.tsupport_wordDerivative_subset X _ _ h)
    simp [this]

end RothschildStein.P1
