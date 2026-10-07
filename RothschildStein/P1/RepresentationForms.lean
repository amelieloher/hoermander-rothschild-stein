-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.RepresentationBasic
public import RothschildStein.P1.Commutation

/-!
# Type-1 forms of `X̃_I(a u)` (no drift, all weights one)

Without drift, the commutation formula has only its first two terms (`noDrift_commutation_of_transfer`): for `T` of
type 1, `X̃ᵢ(T g) = ∑ⱼ T_ij (X̃ⱼ g) + T_i0 g` with `T_ij, T_i0` again of type 1. A *type-1 form* of
level `(nJ, nK)` of `X̃_I(a u)` is
`∑_{|J| ≤ nJ} G_J (X̃_J L̃u) + ∑_{|K| ≤ nK} H_K (X̃_K u)` with `G_J, H_K` of type 1
(`HasRepForm`). One left derivative raises the levels by one (`hasRepForm_cons`): each term
`G_J (X̃_J v)` commutes to `∑ⱼ G_Jj (X̃_j X̃_J v) + G_J0 (X̃_J v)`, the words of length at most `nJ`
(resp. `nK`) grow to at most `nJ + 1` (resp. `nK + 1`). The coefficients are collected by words
(`rep_formStep`), using the splitting `sum_repWords_succ` of the words of length at most `n + 1`.
The level-1 form of `X̃_l(a u)` is `representation_typeOneForm_noDrift_of`; so a word of length
`m ≥ 1` has a type-1 form of level `(m - 1, m)` (`hasRepForm_length`). This is the induction behind the
higher-order representation (BB pp. 565–566, Thm 11.28), organized so that the endpoint invariant is only needed for
the last derivative (`RepresentationHigher`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped Topology BigOperators
namespace RothschildStein.P1

variable {N k : ℕ} {F : KernelFrame N} {w : Fin k → ℕ+}
  {Xt : Fin k → (Fin N → ℝ) → (Fin N → ℝ)}

/-- The no-drift commutation used for every step: for `T` of type 1 and a generator `i`,
`X̃ᵢ(T f) = ∑ⱼ T_ij X̃ⱼ f + T_i0 f` weakly on `V`, for all tests `f` (the commutation formula without drift, `lam = 1`). -/
def RepComm (F : KernelFrame N) (Xt : Fin k → (Fin N → ℝ) → (Fin N → ℝ)) : Prop :=
  ∀ (T : TypeOperator F 1) (i : Fin k),
    ∃ (Fh : Fin k → TypeOperator F 1) (F0 : TypeOperator F 1),
      ∀ f : TestFunction F.V ℝ (⊤ : ℕ∞),
        hasWeakWordDeriv Xt F.V [i] (T.apply f)
          (fun ξ => (∑ j, (Fh j).apply (fieldDerivative (Xt j) (f : (Fin N → ℝ) → ℝ)) ξ) +
            F0.apply f ξ)

/-- The no-drift commutation formula gives `RepComm`. -/
theorem repComm_of_transfer (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (F.V : Set (Fin N → ℝ)))
    (hw : ∀ j, (w j : ℕ) = 1) (B : Fin N → List (Fin k)) (hRowInt : TypeKernelIntegrable F)
    (hRightDiff : RightDifferentiation F w Xt hXt) (hTransfer : DerivativeTransfer F w Xt B) : RepComm F Xt := fun T i => by
  obtain ⟨Fh, F0, h⟩ := noDrift_commutation_of_transfer hXt hw B hRowInt hRightDiff hTransfer le_rfl T i
  exact ⟨Fh, F0, h⟩

/-- The family-indexed type-1 form
`∑_{|J| ≤ nJ} G_J (X̃_J (Lap u)) + ∑_{|K| ≤ nK} H_K (X̃_K u)`. -/
def RepForm (Xt : Fin k → (Fin N → ℝ) → (Fin N → ℝ))
    (Lap : TestFunction F.V ℝ (⊤ : ℕ∞) → TestFunction F.V ℝ (⊤ : ℕ∞))
    (G H : List (Fin k) → TypeOperator F 1) (nJ nK : ℕ) (u : TestFunction F.V ℝ (⊤ : ℕ∞))
    (ξ : Fin N → ℝ) : ℝ :=
  (∑ J ∈ repWords k nJ, (G J).apply (wordDerivative Xt J (Lap u : (Fin N → ℝ) → ℝ)) ξ) +
    ∑ K ∈ repWords k nK, (H K).apply (wordDerivative Xt K (u : (Fin N → ℝ) → ℝ)) ξ

/-- `X̃_I(a u)` has a type-1 form of level `(nJ, nK)` (in terms of `Lap u` and `u`). -/
def HasRepForm (F : KernelFrame N) (Xt : Fin k → (Fin N → ℝ) → (Fin N → ℝ))
    (Lap : TestFunction F.V ℝ (⊤ : ℕ∞) → TestFunction F.V ℝ (⊤ : ℕ∞))
    (a : TestFunction F.V ℝ (⊤ : ℕ∞)) (I : List (Fin k)) (nJ nK : ℕ) : Prop :=
  ∃ G H : List (Fin k) → TypeOperator F 1,
    ∀ u : TestFunction F.V ℝ (⊤ : ℕ∞),
      hasWeakWordDeriv Xt F.V I (fun x => a x * u x) (RepForm Xt Lap G H nJ nK u)

/-- One commutation step on a family: the weak `X̃ᵢ`-derivative of
`∑_{|J| ≤ n} G_J (X̃_J v)` is `∑_{|J| ≤ n + 1} G'_J (X̃_J v)` with one family `G'` of type-1
operators (independent of the test `v`). -/
theorem rep_formStep (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (F.V : Set (Fin N → ℝ)))
    (hRowInt : TypeKernelIntegrable F) (hcomm : RepComm F Xt) (i : Fin k) (n : ℕ)
    (G : List (Fin k) → TypeOperator F 1) :
    ∃ G' : List (Fin k) → TypeOperator F 1, ∀ v : TestFunction F.V ℝ (⊤ : ℕ∞),
      hasWeakWordDeriv Xt F.V [i]
        (fun ξ => ∑ J ∈ repWords k n, (G J).apply (wordDerivative Xt J (v : (Fin N → ℝ) → ℝ)) ξ)
        (fun ξ => ∑ J ∈ repWords k (n + 1),
          (G' J).apply (wordDerivative Xt J (v : (Fin N → ℝ) → ℝ)) ξ) := by
  classical
  choose CH C0 hC using fun T : TypeOperator F 1 => hcomm T i
  let A : List (Fin k) → TypeOperator F 1 := fun J => match J with
    | [] => TypeOperator.zero F 1
    | j :: J' => CH (G J') j
  let Bf : List (Fin k) → TypeOperator F 1 := fun J =>
    if J.length ≤ n then C0 (G J) else TypeOperator.zero F 1
  refine ⟨fun J => (A J).add (Bf J), fun v => ?_⟩
  have hsum := repWeak_finset_sum hXt [i] (repWords k n)
    (fun J ξ => (G J).apply (wordDerivative Xt J (v : (Fin N → ℝ) → ℝ)) ξ)
    (fun J ξ => (∑ j, (CH (G J) j).apply
        (fieldDerivative (Xt j) (wordDerivative Xt J (v : (Fin N → ℝ) → ℝ))) ξ) +
      (C0 (G J)).apply (wordDerivative Xt J (v : (Fin N → ℝ) → ℝ)) ξ)
    (fun J _ => hC (G J) (S.wordDerivativeTest F.V Xt hXt J v))
  refine repWeak_congr hsum (fun _ _ => rfl) (fun x _ => ?_)
  have hti : ∀ J : List (Fin k), IsTestInput (wordDerivative Xt J (v : (Fin N → ℝ) → ℝ)) :=
    fun J => isTestInput_wordDerivative hXt J v
  have hpos : (1 : ℕ) ≠ 0 := by norm_num
  simp only [TypeOperator.apply_add hRowInt hpos _ _ (hti _), Finset.sum_add_distrib]
  rw [sum_repWords_succ (fun J => (A J).apply (wordDerivative Xt J (v : (Fin N → ℝ) → ℝ)) x)]
  have hA : (A []).apply (wordDerivative Xt [] (v : (Fin N → ℝ) → ℝ)) x = 0 :=
    TypeOperator.apply_zero hpos _ x
  have hB : ∑ J ∈ repWords k (n + 1),
      (Bf J).apply (wordDerivative Xt J (v : (Fin N → ℝ) → ℝ)) x =
      ∑ J ∈ repWords k n, (C0 (G J)).apply (wordDerivative Xt J (v : (Fin N → ℝ) → ℝ)) x := by
    symm
    rw [← Finset.sum_subset (s₁ := repWords k n) (s₂ := repWords k (n + 1))
      (f := fun J => (Bf J).apply (wordDerivative Xt J (v : (Fin N → ℝ) → ℝ)) x)]
    · refine Finset.sum_congr rfl fun J hJ => ?_
      have : J.length ≤ n := mem_repWords.1 hJ
      simp only [Bf, this, ↓reduceIte]
    · intro J hJ
      exact mem_repWords.2 (by have := mem_repWords.1 hJ; omega)
    · intro J _ hJ
      have : ¬ J.length ≤ n := fun h => hJ (mem_repWords.2 h)
      simp only [Bf, this, ↓reduceIte]
      exact TypeOperator.apply_zero hpos _ x
  rw [hA, hB, zero_add, Finset.sum_comm]
  rfl

/-- Induction step: if `X̃_I(a u)` has a type-1 form of level `(nJ, nK)`, then `X̃ᵢ X̃_I(a u)`
has one of level `(nJ + 1, nK + 1)` (the no-drift commutation `RepComm` applied to every term,
BB pp. 565–566, Thm 11.28). -/
theorem hasRepForm_cons (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (F.V : Set (Fin N → ℝ)))
    (hRowInt : TypeKernelIntegrable F) (hcomm : RepComm F Xt)
    (Lap : TestFunction F.V ℝ (⊤ : ℕ∞) → TestFunction F.V ℝ (⊤ : ℕ∞))
    {a : TestFunction F.V ℝ (⊤ : ℕ∞)} {I : List (Fin k)} {nJ nK : ℕ}
    (h : HasRepForm F Xt Lap a I nJ nK) (i : Fin k) :
    HasRepForm F Xt Lap a (i :: I) (nJ + 1) (nK + 1) := by
  obtain ⟨G, H, hGH⟩ := h
  obtain ⟨G', hG'⟩ := rep_formStep hXt hRowInt hcomm i nJ G
  obtain ⟨H', hH'⟩ := rep_formStep hXt hRowInt hcomm i nK H
  refine ⟨G', H', fun u => ?_⟩
  exact (S.hasWeakWordDeriv_cons_iff Xt F.V hXt (hGH u) i).mpr
    (S.hasWeakWordDeriv_add Xt F.V hXt (hG' (Lap u)) (hH' u))

end RothschildStein.P1
