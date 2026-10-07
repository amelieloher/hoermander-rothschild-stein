-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ParametrixStatements
public import RothschildStein.P1.TypeClosure
public import RothschildStein.S.WeakDeriv
public import RothschildStein.S.ClassicalWords

/-!
# Basic representations on a lifted chart

Common ingredients of the first-order, second-order and higher-order representations of `X̃_I(a u)` (BB pp. 564–566,
Thms 11.26, 11.28, Cor 11.27):

* `exists_cutoff_mul_eq`: for `a ∈ C_c^∞(V)` there is `b ∈ C_c^∞(V)` with `a b = a` ("choose
  `b = 1` near the support of `a`");
* `exists_zeroth_rep`: from `SignedParametrix` (for the cutoff `a` and every `b`) and the density data, `a f = P₂ (L̃ f) + F₂ f` on `V`
  for tests `f`, with `P₂` of type 2 and `F₂` of type 1;
* `IsEndpoint`: a type-0 operator is an *endpoint operator*, a finite sum `∑ₜ X̃_{jₜ} Gₜ` with
  `Gₜ` of type 1, in the sense of weak derivatives on tests (the structural record of "endpoint"
  in the first-order and higher-order representations); `MultEndpoint` is a coefficient of the
  drift representation `X̃₀(a u) = …`: a smooth multiplication operator
  plus a finite real combination of endpoint operators;
* `exists_leftOp_of_eq`: left differentiation (`LeftDifferentiation`) as a function of the operator;
* `repWords k n`: the finite set of words over `Fin k` of length at most `n`, with its splitting
  `sum_repWords_succ` (empty word plus first letter and a shorter word);
* congruence and finite sums of weak derivatives on `V`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped Topology
namespace RothschildStein.P1

section Cutoff

variable {n : ℕ}

/-- "Choose `b = 1` near the support of `a`": for every `a ∈ C_c^∞(Ω)` there is
`b ∈ C_c^∞(Ω)` with `a b = a`. -/
theorem exists_cutoff_mul_eq (Ω : Opens (Fin n → ℝ)) (a : TestFunction Ω ℝ (⊤ : ℕ∞)) :
    ∃ b : TestFunction Ω ℝ (⊤ : ℕ∞), ∀ ξ, a ξ * b ξ = a ξ := by
  obtain ⟨W, hW, hKW, hclW, hcW⟩ :=
    exists_open_between_and_isCompact_closure a.hasCompactSupport Ω.isOpen a.tsupport_subset
  obtain ⟨χ, hχ, _, hs, hχone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hW (isClosed_tsupport _) hKW
  have ht : tsupport χ ⊆ Ω := by
    rw [tsupport, hs]
    exact hclW
  refine ⟨⟨χ, hχ, by simpa [HasCompactSupport, tsupport, hs] using hcW, ht⟩, fun ξ => ?_⟩
  by_cases hξ : ξ ∈ tsupport (a : (Fin n → ℝ) → ℝ)
  · change a ξ * χ ξ = a ξ
    rw [(hχone ξ).mp hξ, mul_one]
  · simp [image_eq_zero_of_notMem_tsupport hξ]

end Cutoff

variable {N k : ℕ} {F : KernelFrame N} {w : Fin k → ℕ+}
  {Xt : Fin k → (Fin N → ℝ) → (Fin N → ℝ)}

/-- The zeroth-order representation extracted from `SignedParametrixOf` (the left pair
`P_L = P₂`, `F_L = F₂`): for `a ∈ C_c^∞(V)` there are `P₂` of type 2 and `F₂` of type 1 with
`a f = P₂ (L̃ f) + F₂ f` on `V` for every test `f` (choose `b = 1` near the support of `a`). -/
theorem exists_zeroth_rep {Lt : ((Fin N → ℝ) → ℝ) → (Fin N → ℝ) → ℝ} {c : (Fin N → ℝ) → ℝ}
    (hc : ContDiffOn ℝ (⊤ : ℕ∞) c (F.V : Set (Fin N → ℝ)))
    (hc0 : ∀ ξ ∈ (F.V : Set (Fin N → ℝ)), 0 < c ξ) (a : TestFunction F.V ℝ (⊤ : ℕ∞))
    (hParametrix : ∀ b : TestFunction F.V ℝ (⊤ : ℕ∞), SignedParametrixOf F Lt c a b) :
    ∃ (P₂ : TypeOperator F 2) (F₂ : TypeOperator F 1),
      ∀ f : TestFunction F.V ℝ (⊤ : ℕ∞), ∀ ξ ∈ (F.V : Set (Fin N → ℝ)),
        a ξ * f ξ = P₂.apply (Lt f) ξ + F₂.apply f ξ := by
  obtain ⟨b, hb⟩ := exists_cutoff_mul_eq F.V a
  obtain ⟨-, P₂, -, F₂, -, -, -, -, -, -, -, h⟩ := hParametrix b hc hc0 hb
  exact ⟨P₂, F₂, h⟩

/-! ### Endpoint operators -/

/-- A type-0 operator `S` is an *endpoint operator*: a finite sum `∑ₜ X̃_{jₜ} Gₜ` with
`Gₜ` of type 1 (BB p. 565, "each `S` is a finite sum of `X̃_j F`, `F` of type 1"); on every test
`g`, `S g` is the sum of the weak `X̃_{jₜ}`-derivatives (on `V`) of `Gₜ g`. -/
def IsEndpoint (F : KernelFrame N) (Xt : Fin k → (Fin N → ℝ) → (Fin N → ℝ))
    (S : TypeOperator F 0) : Prop :=
  ∃ (r : ℕ) (j : Fin r → Fin k) (G : Fin r → TypeOperator F 1),
    ∀ g : TestFunction F.V ℝ (⊤ : ℕ∞), ∃ h : Fin r → (Fin N → ℝ) → ℝ,
      (∀ t, hasWeakWordDeriv Xt F.V [j t] ((G t).apply g) (h t)) ∧
      S.apply g = fun ξ => ∑ t, h t ξ

/-- A single term `S = X̃_j G`, `G` of type 1, is an endpoint operator. -/
theorem IsEndpoint.of_weakDeriv {S : TypeOperator F 0} {j : Fin k} {G : TypeOperator F 1}
    (h : ∀ g : TestFunction F.V ℝ (⊤ : ℕ∞), hasWeakWordDeriv Xt F.V [j] (G.apply g) (S.apply g)) :
    IsEndpoint F Xt S :=
  ⟨1, fun _ => j, fun _ => G, fun g => ⟨fun _ => S.apply g, fun _ => h g, by
    funext ξ
    simp⟩⟩

/-! ### Words -/

/-- The finite set of words over `Fin k` of length at most `n`. -/
def repWords (k : ℕ) : ℕ → Finset (List (Fin k))
  | 0 => {[]}
  | n + 1 => insert []
      (((Finset.univ : Finset (Fin k)) ×ˢ repWords k n).image fun p => p.1 :: p.2)

/-- Membership in the words of length at most `n`. -/
theorem mem_repWords {n : ℕ} {J : List (Fin k)} : J ∈ repWords k n ↔ J.length ≤ n := by
  induction n generalizing J with
  | zero => simp [repWords]
  | succ n ih =>
    cases J with
    | nil => simp [repWords]
    | cons j J =>
      simp only [repWords, Finset.mem_insert, List.cons_ne_nil, false_or, Finset.mem_image,
        Finset.mem_product, Finset.mem_univ, true_and, Prod.exists, List.cons.injEq,
        List.length_cons]
      constructor
      · rintro ⟨a, b, hb, rfl, rfl⟩
        exact Nat.succ_le_succ (ih.1 hb)
      · intro h
        exact ⟨j, J, ih.2 (by omega), rfl, rfl⟩

/-- A sum over the words of length at most `n + 1` splits into the empty word and the words
`j :: J` with `|J| ≤ n`. -/
theorem sum_repWords_succ {M : Type*} [AddCommMonoid M] (g : List (Fin k) → M) (n : ℕ) :
    ∑ J ∈ repWords k (n + 1), g J = g [] + ∑ j : Fin k, ∑ J ∈ repWords k n, g (j :: J) := by
  rw [repWords, Finset.sum_insert (by simp), Finset.sum_image, Finset.sum_product]
  intro p _ q _ h
  exact Prod.ext (List.cons.inj h).1 (List.cons.inj h).2

/-- The words of length at most `0` are the empty word. -/
theorem repWords_zero : repWords k 0 = {[]} := rfl

/-! ### Weak derivatives on `V` -/

/-- Weak derivatives only depend on the functions on `V`. -/
theorem repWeak_congr {I : List (Fin k)} {f f' g g' : (Fin N → ℝ) → ℝ}
    (h : hasWeakWordDeriv Xt F.V I f g) (hf : ∀ x ∈ (F.V : Set (Fin N → ℝ)), f x = f' x)
    (hg : ∀ x ∈ (F.V : Set (Fin N → ℝ)), g x = g' x) : hasWeakWordDeriv Xt F.V I f' g' :=
  S.hasWeakWordDeriv_congr_ae Xt F.V h
    ((ae_restrict_iff' F.V.isOpen.measurableSet).2 (Filter.Eventually.of_forall hf))
    ((ae_restrict_iff' F.V.isOpen.measurableSet).2 (Filter.Eventually.of_forall hg))

/-- Finite sums of weak derivatives. -/
theorem repWeak_finset_sum (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (F.V : Set (Fin N → ℝ)))
    {ι : Type*} (I : List (Fin k)) (s : Finset ι)
    (f g : ι → (Fin N → ℝ) → ℝ) (h : ∀ a ∈ s, hasWeakWordDeriv Xt F.V I (f a) (g a)) :
    hasWeakWordDeriv Xt F.V I (fun x => ∑ a ∈ s, f a x) (fun x => ∑ a ∈ s, g a x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using S.hasWeakWordDeriv_zero Xt F.V I
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact S.hasWeakWordDeriv_add Xt F.V hXt (h a (Finset.mem_insert_self a s))
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

/-- Sum of three weak derivatives. -/
theorem repWeak_add₃ (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (F.V : Set (Fin N → ℝ)))
    {I : List (Fin k)} {f₁ f₂ f₃ g₁ g₂ g₃ : (Fin N → ℝ) → ℝ}
    (h₁ : hasWeakWordDeriv Xt F.V I f₁ g₁) (h₂ : hasWeakWordDeriv Xt F.V I f₂ g₂)
    (h₃ : hasWeakWordDeriv Xt F.V I f₃ g₃) :
    hasWeakWordDeriv Xt F.V I (fun x => f₁ x + f₂ x + f₃ x) (fun x => g₁ x + g₂ x + g₃ x) :=
  S.hasWeakWordDeriv_add Xt F.V hXt (S.hasWeakWordDeriv_add Xt F.V hXt h₁ h₂) h₃

/-- Left differentiation of an operator by a generator, from `LeftDifferentiation`: for `T` of type
`lam`, `w i ≤ lam` and `lam - w i = lam'` there is a type-`lam'` operator `S` with
`X̃ᵢ (T g) = S g` (weak derivative on `V`) for every test `g`. -/
theorem exists_leftOp_of_eq (hLeftDiff : LeftDifferentiation F w Xt) {lam lam' : ℕ} (T : TypeOperator F lam)
    (i : Fin k) (hi : (w i : ℕ) ≤ lam) (h : lam - (w i : ℕ) = lam') :
    ∃ S : TypeOperator F lam', ∀ g : TestFunction F.V ℝ (⊤ : ℕ∞),
      hasWeakWordDeriv Xt F.V [i] (T.apply g) (S.apply g) := by
  obtain ⟨S, hS⟩ := hLeftDiff lam T i hi
  refine ⟨S.ofEq h, fun g => ?_⟩
  have e : (S.ofEq h).apply (g : (Fin N → ℝ) → ℝ) = S.apply g :=
    funext fun ξ => TypeOperator.apply_ofEq h S _ ξ
  rw [e]
  exact hS g

end RothschildStein.P1
