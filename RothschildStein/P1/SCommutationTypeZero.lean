-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.SCommutationEndpoint

/-!
# No-drift commutation: the commuted operators have endpoint type 0

The endpoint operators `X̃ᵢ C` of `SCommutationEndpoint` (`C` of type `1`) are operators of type
`0` by left differentiation (`LeftDifferentiation`: for type `lam ≥ w i`, `X̃ᵢ T` has type `lam - w i`,
here `1 - 1 = 0`). The conclusion "all new coefficients are endpoint type 0; every
`X̃_I S f` is a finite sum of endpoint type-0 operators applied to `X̃_J f`, `|J| ≤ |I|`"
(BB pp. 567–568, Prop 11.31) is therefore the corollary of the endpoint commutation theorems under
the additional exact upstream statement `LeftDifferentiation`; the finite sums of type-0 operators are then
estimated term by term by the `L^p` and Hölder continuity of type-`0` operators.

At type 0 the action is a principal value, whose additivity in the operator is not asserted; the
sums over `J` are therefore kept as finite sums of single operators (lists for a family).
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

/-- Endpoint type 0 (left differentiation, no drift): for a type-1 operator `C` and a
generator `i` there is a type-0 operator `T` with `T g` the weak `X̃ᵢ`-derivative of `C g` for
every test `g`. -/
theorem exists_typeZero_weakDeriv (hw : ∀ j, (w j : ℕ) = 1) (hLeftDiff : LeftDifferentiation F w Xt)
    (C : TypeOperator F 1) (i : Fin k) :
    ∃ T : TypeOperator F 0, ∀ g : TestFunction F.V ℝ (⊤ : ℕ∞),
      hasWeakWordDeriv Xt F.V [i] (C.apply (g : (Fin N → ℝ) → ℝ)) (T.apply (g : (Fin N → ℝ) → ℝ)) := by
  obtain ⟨T, hT⟩ := hLeftDiff 1 C i (le_of_eq (hw i))
  have h : 1 - (w i : ℕ) = 0 := by rw [hw i]
  refine ⟨T.ofEq h, fun g => ?_⟩
  have e : (T.ofEq h).apply (g : (Fin N → ℝ) → ℝ) = T.apply (g : (Fin N → ℝ) → ℝ) :=
    funext fun ξ => TypeOperator.apply_ofEq h T _ ξ
  rw [e]
  exact hT g

section Hypotheses

variable (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (F.V : Set (Fin N → ℝ)))
  (hw : ∀ j, (w j : ℕ) = 1) (B : Fin N → List (Fin k))
  (hRowInt : TypeKernelIntegrable F) (hRightDiff : RightDifferentiation F w Xt hXt) (hTransfer : DerivativeTransfer F w Xt B)
  (hLeftDiff : LeftDifferentiation F w Xt)
include hXt hw hRowInt hRightDiff hTransfer hLeftDiff

/-- Commuting `X̃_I` with the endpoint family `S`, no drift, endpoint type 0 (BB pp. 567–568,
Prop 11.31). Assume the type-calculus hypotheses of the commutation formula
(`TypeKernelIntegrable`, `RightDifferentiation`, `DerivativeTransfer`) and left differentiation (`LeftDifferentiation`). For
`S = ∑ₗ X̃_{iₗ} Cₗ` with
`Cₗ` of type `1` and every nonempty word `i :: I`, there are type-1 operators `C_J` and type-0
operators `T_J = X̃ᵢ C_J` (`T_J g` is the weak `X̃ᵢ`-derivative of `C_J g`), one for each word `J`
with `|J| ≤ |i :: I|`, such that on tests, weakly on `V`,
`X̃_{i :: I} (S f) = ∑_J T_J (X̃_J f)`. -/
theorem noDrift_typeZero_commutation_cons_of_transfer (E : EndpointSum F Xt) (i : Fin k)
    (I : List (Fin k)) :
    ∃ (C : List (Fin k) → TypeOperator F 1) (T : List (Fin k) → TypeOperator F 0),
      (∀ (J : List (Fin k)) (g : TestFunction F.V ℝ (⊤ : ℕ∞)),
        hasWeakWordDeriv Xt F.V [i] ((C J).apply (g : (Fin N → ℝ) → ℝ))
          ((T J).apply (g : (Fin N → ℝ) → ℝ))) ∧
      ∀ f : TestFunction F.V ℝ (⊤ : ℕ∞),
        hasWeakWordDeriv Xt F.V (i :: I) (endpointApply E f)
          (fun ξ => ∑ J ∈ wordsUpTo k (i :: I).length,
            (T J).apply (wordDerivative Xt J (f : (Fin N → ℝ) → ℝ)) ξ) := by
  obtain ⟨C, hC⟩ := exists_collected_endpoint_form hXt hw B hRowInt hRightDiff hTransfer E I
  choose T hT using fun C : TypeOperator F 1 => exists_typeZero_weakDeriv hw hLeftDiff C i
  refine ⟨C, fun J => T (C J), fun J g => hT (C J) g, fun f => ?_⟩
  have hsum := hasWeakWordDeriv_finset_sum hXt [i] (wordsUpTo k (I.length + 1))
    (fun J => (C J).apply (wordDerivative Xt J (f : (Fin N → ℝ) → ℝ)))
    (fun J => (T (C J)).apply (wordDerivative Xt J (f : (Fin N → ℝ) → ℝ)))
    (fun J _ => hT (C J) (S.wordDerivativeTest F.V Xt hXt J f))
  have hlen : (i :: I).length = I.length + 1 := rfl
  rw [hlen]
  exact (S.hasWeakWordDeriv_cons_iff Xt F.V hXt (hC f) i).2 hsum

/-- The finite data `𝒟_{S,n}` with endpoint type 0 (BB pp. 567–568, Prop 11.31): for the
endpoint family `S = ∑ₗ X̃_{iₗ} Cₗ` (`Cₗ` of type `1`) there are finite lists `S_{I,J}` of type-0
operators, one for every pair of words, such that for **every** word `I`, on tests and weakly on
`V`,
`X̃_I (S f) = ∑_{J ∈ wordsUpTo k |I|} ∑_{T ∈ S_{I,J}} T (X̃_J f)`.
For `I = []` the list `S_{[],[]}` consists of the type-0 operators `X̃_{iₗ} Cₗ` of `S` itself; for
nonempty `I` each `S_{I,J}` is the single type-0 operator `X̃ᵢ C_{I,J}`. Assume
`TypeKernelIntegrable`, `RightDifferentiation`, `DerivativeTransfer` and `LeftDifferentiation`. -/
theorem noDrift_typeZero_commutedFamily_of_transfer (E : EndpointSum F Xt) :
    ∃ Tfam : List (Fin k) → List (Fin k) → List (TypeOperator F 0),
      ∀ (I : List (Fin k)) (f : TestFunction F.V ℝ (⊤ : ℕ∞)),
        hasWeakWordDeriv Xt F.V I (endpointApply E f)
          (fun ξ => ∑ J ∈ wordsUpTo k I.length,
            ((Tfam I J).map fun T =>
              T.apply (wordDerivative Xt J (f : (Fin N → ℝ) → ℝ)) ξ).sum) := by
  classical
  choose Te hTe using fun e : EndpointOp F Xt => exists_typeZero_weakDeriv hw hLeftDiff e.op e.letter
  have key : ∀ I : List (Fin k), ∃ TIJ : List (Fin k) → List (TypeOperator F 0),
      ∀ f : TestFunction F.V ℝ (⊤ : ℕ∞),
        hasWeakWordDeriv Xt F.V I (endpointApply E f)
          (fun ξ => ∑ J ∈ wordsUpTo k I.length,
            ((TIJ J).map fun T =>
              T.apply (wordDerivative Xt J (f : (Fin N → ℝ) → ℝ)) ξ).sum) := by
    intro I
    cases I with
    | nil =>
      refine ⟨fun J => if J = [] then E.map Te else [], fun f => ?_⟩
      have hl : ∀ e ∈ E, hasWeakWordDeriv Xt F.V [] (e.out f)
          ((Te e).apply (f : (Fin N → ℝ) → ℝ)) := by
        intro e _
        have hae := S.hasWeakWordDeriv_unique Xt F.V (e.weak f) (hTe e f)
        have h0 := S.hasWeakWordDeriv_nil Xt F.V (hTe e f).2.1
        exact S.hasWeakWordDeriv_congr_ae Xt F.V h0 hae.symm Filter.EventuallyEq.rfl
      have hsum := S.hasWeakWordDeriv_list_sum Xt F.V hXt [] E (fun e => e.out f)
        (fun e => (Te e).apply (f : (Fin N → ℝ) → ℝ)) hl
      have e : (fun ξ => ∑ J ∈ wordsUpTo k ([] : List (Fin k)).length,
          (((fun J => if J = [] then E.map Te else []) J).map fun T =>
            T.apply (wordDerivative Xt J (f : (Fin N → ℝ) → ℝ)) ξ).sum) =
          fun x => (E.map fun e => (Te e).apply (f : (Fin N → ℝ) → ℝ) x).sum := by
        funext ξ
        simp [wordsUpTo_zero, wordDerivative, List.map_map, Function.comp_def]
      rw [e]
      exact hsum
    | cons i I =>
      obtain ⟨C, T, -, hweak⟩ :=
        noDrift_typeZero_commutation_cons_of_transfer hXt hw B hRowInt hRightDiff hTransfer hLeftDiff E i I
      refine ⟨fun J => [T J], fun f => ?_⟩
      have e : (fun ξ => ∑ J ∈ wordsUpTo k (i :: I).length,
          (((fun J => [T J]) J).map fun T =>
            T.apply (wordDerivative Xt J (f : (Fin N → ℝ) → ℝ)) ξ).sum) = fun ξ =>
          ∑ J ∈ wordsUpTo k (i :: I).length,
            (T J).apply (wordDerivative Xt J (f : (Fin N → ℝ) → ℝ)) ξ := by
        funext ξ
        simp
      rw [e]
      exact hweak f
  choose Tfam hTfam using key
  exact ⟨Tfam, hTfam⟩

/-- **No-drift commutation of `X̃_I` with `S = ∑ⱼ X̃ⱼ Fⱼ`, endpoint type 0** (BB pp. 567–568,
Prop 11.31): for any family `Fⱼ` of type-1
operators, with `S f = ∑ⱼ (E j).out f` (`(E j).out f` the weak `X̃ⱼ`-derivative of `Fⱼ f`), there
are finite lists `S_{I,J}` of type-0 operators (the finite family `𝒟_{S,n}` is
`{S_{I,J} | |J| ≤ |I| ≤ n}`) with
`X̃_I (S f) = ∑_{|J| ≤ |I|} ∑_{T ∈ S_{I,J}} T (X̃_J f)`
for every word `I` and test `f`, weakly on `V`, assuming `TypeKernelIntegrable`, `RightDifferentiation`,
`DerivativeTransfer` and `LeftDifferentiation`. -/
theorem noDrift_typeZero_commutedFamily_of_endpointFamily_of_transfer
    (Fj : Fin k → TypeOperator F 1) :
    ∃ (E : Fin k → EndpointOp F Xt) (Tfam : List (Fin k) → List (Fin k) → List (TypeOperator F 0)),
      (∀ j, (E j).letter = j ∧ (E j).op = Fj j) ∧
      ∀ (I : List (Fin k)) (f : TestFunction F.V ℝ (⊤ : ℕ∞)),
        hasWeakWordDeriv Xt F.V I (fun ξ => ∑ j, (E j).out f ξ)
          (fun ξ => ∑ J ∈ wordsUpTo k I.length,
            ((Tfam I J).map fun T =>
              T.apply (wordDerivative Xt J (f : (Fin N → ℝ) → ℝ)) ξ).sum) := by
  obtain ⟨E, hE⟩ := exists_endpointFamily hXt hw B hRowInt hRightDiff hTransfer Fj
  obtain ⟨Tfam, hTfam⟩ := noDrift_typeZero_commutedFamily_of_transfer hXt hw B hRowInt hRightDiff hTransfer hLeftDiff
    ((List.finRange k).map E)
  refine ⟨E, Tfam, hE, fun I f => ?_⟩
  have e : endpointApply ((List.finRange k).map E) f = fun ξ => ∑ j, (E j).out f ξ := by
    funext ξ
    simp [endpointApply, Fin.sum_univ_def, List.map_map, Function.comp_def]
  have := hTfam I f
  rwa [e] at this

end Hypotheses

end RothschildStein.P1
