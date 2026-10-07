-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.SCommutation

/-!
# No-drift commutation of `X̃_I` with `S = ∑ⱼ X̃ⱼ Fⱼ`

Without drift (all weights one), let `S = ∑ⱼ X̃ⱼ Fⱼ` with `Fⱼ` of type `1` (an *endpoint family*;
BB p. 567, proof of Prop 11.31). Here `X̃ⱼ Fⱼ` is the weak
`X̃ⱼ`-derivative on `V` of `Fⱼ f`, carried together with a chosen representative (`EndpointOp`).

Proof (the commutation formula gives `X̃ᵢ S = ∑ₕ (X̃ᵢ F_h) X̃ₕ + X̃ᵢ F₀`; repeat):

* the commutation formula turns `X̃ⱼ (Fⱼ f)` into the type-1 form `∑ₕ F_{jh} (X̃ₕ f) + F_{j0} f` with words of length
  at most one (`exists_form_of_endpointSum`);
* the inner derivatives `X̃_{I'}` of a type-1 form are again type-1 forms, with the word length
  raised by `|I'|` (`exists_form_word`);
* the outermost derivative `X̃ᵢ` of `∑_J C_J (X̃_J f)` is the endpoint sum `∑_J (X̃ᵢ C_J)(X̃_J f)`,
  whose terms are endpoint operators `X̃ᵢ C_J` with `C_J` of type `1`.

Hence `X̃_{i :: I} (S f) = ∑_{|J| ≤ |i :: I|} (X̃ᵢ C_J)(X̃_J f)`: no derivative is lost on `f`
(`noDrift_endpoint_commutation_cons_of_transfer`). The finite family `𝒟_{S,n}` of all commuted
endpoint operators through level `n` is `noDrift_commutedFamily_of_transfer`.
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

/-- An *endpoint operator* `X̃ᵢ C` with `C` of type `1` (BB p. 567: `S = ∑ⱼ X̃ⱼ Fⱼ`,
`Fⱼ` type `1`): the type-1 operator `op`, the generator `letter`, and a representative `out g` of
the weak `X̃_letter`-derivative on `V` of `op g`, for every test `g`. -/
structure EndpointOp (F : KernelFrame N) (Xt : Fin k → (Fin N → ℝ) → (Fin N → ℝ)) where
  /-- The generator `i` of `X̃ᵢ C`. -/
  letter : Fin k
  /-- The type-1 operator `C`. -/
  op : TypeOperator F 1
  /-- A representative of the weak derivative `X̃ᵢ (C g)`. -/
  out : TestFunction F.V ℝ (⊤ : ℕ∞) → (Fin N → ℝ) → ℝ
  /-- `out g` is the weak `X̃ᵢ`-derivative on `V` of `C g`. -/
  weak : ∀ g : TestFunction F.V ℝ (⊤ : ℕ∞),
    hasWeakWordDeriv Xt F.V [letter] (op.apply (g : (Fin N → ℝ) → ℝ)) (out g)

/-- An *endpoint sum* `S = ∑ₗ X̃_{iₗ} Cₗ`: a finite list of endpoint operators (the
endpoint family `S = ∑ⱼ X̃ⱼ Fⱼ` of the higher-order gain, and each commuted operator `S_{I,J}`). -/
abbrev EndpointSum (F : KernelFrame N) (Xt : Fin k → (Fin N → ℝ) → (Fin N → ℝ)) : Type :=
  List (EndpointOp F Xt)

/-- The action `S g = ∑ₗ X̃_{iₗ} (Cₗ g)` of an endpoint sum on a test `g`. -/
def endpointApply (E : EndpointSum F Xt) (g : TestFunction F.V ℝ (⊤ : ℕ∞)) (ξ : Fin N → ℝ) : ℝ :=
  (E.map fun e => e.out g ξ).sum

/-- The empty endpoint sum is zero. -/
theorem endpointApply_nil (g : TestFunction F.V ℝ (⊤ : ℕ∞)) :
    endpointApply ([] : EndpointSum F Xt) g = fun _ => 0 := by
  funext ξ
  simp [endpointApply]

/-- An endpoint sum splits into its first term and the rest. -/
theorem endpointApply_cons (e : EndpointOp F Xt) (E : EndpointSum F Xt)
    (g : TestFunction F.V ℝ (⊤ : ℕ∞)) (ξ : Fin N → ℝ) :
    endpointApply (e :: E) g ξ = e.out g ξ + endpointApply E g ξ := by
  simp [endpointApply]

section Hypotheses

variable (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (F.V : Set (Fin N → ℝ)))
  (hw : ∀ j, (w j : ℕ) = 1) (B : Fin N → List (Fin k))
  (hRowInt : TypeKernelIntegrable F) (hRightDiff : RightDifferentiation F w Xt hXt) (hTransfer : DerivativeTransfer F w Xt B)
include hXt hw hRowInt hRightDiff hTransfer

/-- An endpoint sum is, weakly of order zero, a type-1 form with words of length at most
one: `X̃ⱼ (Fⱼ f) = ∑ₕ F_{jh} (X̃ₕ f) + F_{j0} f` (the commutation formula without drift, `lam = 1`), summed over the
terms. -/
theorem exists_form_of_endpointSum (E : EndpointSum F Xt) :
    ∃ L : List (TypeOneTerm F k), (∀ p ∈ L, p.1.length ≤ 1) ∧
      ∀ f : TestFunction F.V ℝ (⊤ : ℕ∞),
        hasWeakWordDeriv Xt F.V [] (endpointApply E f) (formApply Xt L f) := by
  induction E with
  | nil =>
    refine ⟨[], by simp, fun f => ?_⟩
    rw [formApply_nil, endpointApply_nil]
    exact S.hasWeakWordDeriv_zero Xt F.V []
  | cons e E ih =>
    obtain ⟨L', hL', hweak⟩ := ih
    obtain ⟨Fh, F0, hFh⟩ :=
      noDrift_commutation_of_transfer hXt hw B hRowInt hRightDiff hTransfer le_rfl e.op e.letter
    refine ⟨((List.finRange k).map fun j => ([j], Fh j)) ++ ([], F0) :: L', ?_, fun f => ?_⟩
    · intro q hq
      rcases List.mem_append.1 hq with hq | hq
      · obtain ⟨j, -, rfl⟩ := List.mem_map.1 hq
        simp
      · rcases List.mem_cons.1 hq with rfl | hq
        · simp
        · exact hL' q hq
    · have hae := S.hasWeakWordDeriv_unique Xt F.V (e.weak f) (hFh f)
      have h0 := S.hasWeakWordDeriv_nil Xt F.V (hFh f).2.1
      have he := S.hasWeakWordDeriv_congr_ae Xt F.V h0 hae.symm Filter.EventuallyEq.rfl
      have h := S.hasWeakWordDeriv_add Xt F.V hXt he (hweak f)
      have e1 : endpointApply (e :: E) f = fun ξ => e.out f ξ + endpointApply E f ξ :=
        funext fun ξ => endpointApply_cons e E f ξ
      have e2 : formApply Xt (((List.finRange k).map fun j => ([j], Fh j)) ++
          ([], F0) :: L') f = fun ξ =>
          ((∑ j, (Fh j).apply (fieldDerivative (Xt j) (f : (Fin N → ℝ) → ℝ)) ξ) +
            F0.apply (f : (Fin N → ℝ) → ℝ) ξ) + formApply Xt L' f ξ := by
        funext ξ
        rw [formApply_append, formApply_cons, formApply]
        simp only [List.map_map, Function.comp_def, wordDerivative, Fin.sum_univ_def]
        ring
      rw [e1, e2]
      exact h

/-- The weak `X̃_I`-derivative of an endpoint sum (`I` any word, possibly empty) is a
type-1 form with words of length at most `|I| + 1`: the inner derivatives `X̃_{I}` of the type-1
form of `exists_form_of_endpointSum` (the iterated commutation formula). -/
theorem exists_form_word_endpointSum (E : EndpointSum F Xt) (I : List (Fin k)) :
    ∃ L : List (TypeOneTerm F k), (∀ p ∈ L, p.1.length ≤ I.length + 1) ∧
      ∀ f : TestFunction F.V ℝ (⊤ : ℕ∞),
        hasWeakWordDeriv Xt F.V I (endpointApply E f) (formApply Xt L f) := by
  obtain ⟨L₁, h₁, hw₁⟩ := exists_form_of_endpointSum hXt hw B hRowInt hRightDiff hTransfer E
  cases I with
  | nil => exact ⟨L₁, by simpa using h₁, hw₁⟩
  | cons a I =>
    obtain ⟨L₂, h₂, hw₂⟩ := exists_form_word hXt hw B hRowInt hRightDiff hTransfer 1 L₁ h₁ I a
    refine ⟨L₂, fun p hp => ?_, fun f => ?_⟩
    · have := h₂ p hp
      simp only [List.length_cons] at this ⊢
      omega
    · have hunique := S.hasWeakWordDeriv_unique Xt F.V
        (S.hasWeakWordDeriv_nil Xt F.V (hw₁ f).1) (hw₁ f)
      exact S.hasWeakWordDeriv_congr_ae Xt F.V (hw₂ f) hunique.symm Filter.EventuallyEq.rfl

/-- The weak `X̃_I`-derivative of an endpoint sum, as a collected type-1 form: there are
type-1 operators `C_J`, one for each word `J` of length at most `|I| + 1`, with
`X̃_I (S f) = ∑_J C_J (X̃_J f)` (weak derivative on `V`, for every test `f`). -/
theorem exists_collected_endpoint_form (E : EndpointSum F Xt) (I : List (Fin k)) :
    ∃ C : List (Fin k) → TypeOperator F 1, ∀ f : TestFunction F.V ℝ (⊤ : ℕ∞),
      hasWeakWordDeriv Xt F.V I (endpointApply E f)
        (fun ξ => ∑ J ∈ wordsUpTo k (I.length + 1),
          (C J).apply (wordDerivative Xt J (f : (Fin N → ℝ) → ℝ)) ξ) := by
  obtain ⟨L, hL, hweak⟩ := exists_form_word_endpointSum hXt hw B hRowInt hRightDiff hTransfer E I
  obtain ⟨C, hC⟩ := exists_collected_form hXt hRowInt (I.length + 1) L hL
  refine ⟨C, fun f => ?_⟩
  have hform : formApply Xt L f = fun ξ => ∑ J ∈ wordsUpTo k (I.length + 1),
      (C J).apply (wordDerivative Xt J (f : (Fin N → ℝ) → ℝ)) ξ := funext (hC f)
  rw [← hform]
  exact hweak f

/-- Every type-1 operator `C` and generator `i` give an endpoint operator `X̃ᵢ C`: the weak
`X̃ᵢ`-derivative of `C g` exists for every test `g` (the commutation formula without drift), so no hypothesis on `S` beyond
the type calculus is needed to form `S = ∑ⱼ X̃ⱼ Fⱼ`. -/
theorem exists_endpointOp (C : TypeOperator F 1) (i : Fin k) :
    ∃ e : EndpointOp F Xt, e.letter = i ∧ e.op = C := by
  obtain ⟨r, hr⟩ := exists_weakDeriv_typeOne hXt hw B hRowInt hRightDiff hTransfer C i
  exact ⟨⟨i, C, r, hr⟩, rfl, rfl⟩

/-- The endpoint family `S = ∑ⱼ X̃ⱼ Fⱼ` of any family `Fⱼ` of type-1 operators exists:
`(E j).op = Fⱼ`, `(E j).letter = j`, and `(E j).out f` is the weak `X̃ⱼ`-derivative of `Fⱼ f`. -/
theorem exists_endpointFamily (Fj : Fin k → TypeOperator F 1) :
    ∃ E : Fin k → EndpointOp F Xt, ∀ j, (E j).letter = j ∧ (E j).op = Fj j := by
  choose e he using fun j => exists_endpointOp hXt hw B hRowInt hRightDiff hTransfer (Fj j) j
  exact ⟨e, he⟩

end Hypotheses

end RothschildStein.P1
