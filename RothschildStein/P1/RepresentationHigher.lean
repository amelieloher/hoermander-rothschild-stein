-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.RepresentationForms

/-!
# Higher-order representation without drift

With no drift (all weights one, `L̃ = ∑ᵢ X̃ᵢ²`), for every word `I` of length `m ≥ 2` and cutoff `a`
there are endpoint type-0 families `S_IJ` (`|J| ≤ m - 2`) and `T_IK` (`|K| ≤ m - 1`) with
`X̃_I(a u) = ∑_J S_IJ X̃_J L̃u + ∑_K T_IK X̃_K u` for every test `u` (BB pp. 565–566, Thm 11.28).

Proof. *Base case*: the level-1 type-1 form of `X̃_l(a u)`,
`X̃_l(a u) = (X̃_l P₂) L̃u + ∑ⱼ F_lj X̃ⱼ u + F_l0 u`, from `a u = P₂ L̃u + F₂ u` (the left pair of
`SignedParametrixNoDrift`), left differentiation of `P₂` (`LeftDifferentiation`) and the no-drift commutation of
`F₂` (`noDrift_commutation_of_transfer`), all coefficients of type 1
(`representation_typeOneForm_noDrift_of`); this is the first-order representation without drift.
*Induction step*: the no-drift commutation formula applied to every coefficient raises the
word lengths by at most one (`hasRepForm_cons`; the left words of `L̃u` have length at most `m - 1`
at level `m`, those of `u` at most `m`). *Last derivative*: the final `X̃_i` acts by left
differentiation (`LeftDifferentiation`) on the type-1 coefficients, which become endpoint operators of type 0
(a single term `X̃_i G`). Collecting by words keeps the invariant (finite sums), without double
counting at `m = 2`: the empty word is the identity.
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

/-- `L̃ u = ∑ᵢ X̃ᵢ² u` of a test function is a test function (no drift). -/
def repSumSquaresTest (F : KernelFrame N) (Xt : Fin k → (Fin N → ℝ) → (Fin N → ℝ))
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (F.V : Set (Fin N → ℝ)))
    (u : TestFunction F.V ℝ (⊤ : ℕ∞)) : TestFunction F.V ℝ (⊤ : ℕ∞) :=
  ∑ i : Fin k, S.wordDerivativeTest F.V Xt hXt [i, i] u

/-- The values of `repSumSquaresTest` are those of `sumSquares`. -/
theorem coe_repSumSquaresTest (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (F.V : Set (Fin N → ℝ)))
    (u : TestFunction F.V ℝ (⊤ : ℕ∞)) :
    (repSumSquaresTest F Xt hXt u : (Fin N → ℝ) → ℝ) = sumSquares Xt u := by
  funext x
  let ev : TestFunction F.V ℝ (⊤ : ℕ∞) →+ ℝ :=
    { toFun := fun φ => φ x, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have h := map_sum ev (fun i : Fin k => S.wordDerivativeTest F.V Xt hXt [i, i] u) Finset.univ
  exact h

/-- The level-1 type-1 form without drift: for `a ∈ C_c^∞(V)` and every
generator `l`, `X̃_l(a u) = G_l L̃u + ∑ⱼ C_lj X̃ⱼ u + C_l0 u` on tests `u` (weak derivative on `V`),
with `G_l, C_lj, C_l0` of type 1 (`G_l = X̃_l P₂`; BB p. 564 without drift). -/
theorem representation_typeOneForm_noDrift_of
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (F.V : Set (Fin N → ℝ)))
    (hw : ∀ j, (w j : ℕ) = 1) (B : Fin N → List (Fin k)) (hRowInt : TypeKernelIntegrable F)
    (hLeftDiff : LeftDifferentiation F w Xt) (hRightDiff : RightDifferentiation F w Xt hXt) (hTransfer : DerivativeTransfer F w Xt B)
    {c : (Fin N → ℝ) → ℝ} (hc : ContDiffOn ℝ (⊤ : ℕ∞) c (F.V : Set (Fin N → ℝ)))
    (hc0 : ∀ ξ ∈ (F.V : Set (Fin N → ℝ)), 0 < c ξ) (a : TestFunction F.V ℝ (⊤ : ℕ∞))
    (hParametrix : ∀ b : TestFunction F.V ℝ (⊤ : ℕ∞), SignedParametrixNoDrift F Xt c a b) :
    ∃ (G : Fin k → TypeOperator F 1) (Cc : Fin k → Fin k → TypeOperator F 1)
      (C0 : Fin k → TypeOperator F 1),
      ∀ (l : Fin k) (u : TestFunction F.V ℝ (⊤ : ℕ∞)),
        hasWeakWordDeriv Xt F.V [l] (fun x => a x * u x)
          (fun ξ => (G l).apply (sumSquares Xt u) ξ +
            (∑ j, (Cc l j).apply (fieldDerivative (Xt j) (u : (Fin N → ℝ) → ℝ)) ξ) +
            (C0 l).apply u ξ) := by
  obtain ⟨P₂, F₂, hzero⟩ := exists_zeroth_rep hc hc0 a hParametrix
  choose Ql hQl using fun l : Fin k =>
    exists_leftOp_of_eq (lam' := 1) hLeftDiff P₂ l (by have := hw l; omega) (by have := hw l; omega)
  choose Fh F0 hcomm using fun l : Fin k =>
    noDrift_commutation_of_transfer hXt hw B hRowInt hRightDiff hTransfer (lam := 1) le_rfl F₂ l
  refine ⟨Ql, Fh, F0, fun l u => ?_⟩
  have h1 := hQl l (repSumSquaresTest F Xt hXt u)
  rw [coe_repSumSquaresTest] at h1
  exact repWeak_congr (S.hasWeakWordDeriv_add Xt F.V hXt h1 (hcomm l u))
    (fun x hx => (hzero u x hx).symm) (fun x _ => by ring)

/-- Level `(0, 1)` of the type-1 forms: `X̃_l(a u)` has a type-1 form with
`J = ∅` and `|K| ≤ 1`. -/
theorem hasRepForm_one
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (F.V : Set (Fin N → ℝ)))
    (hw : ∀ j, (w j : ℕ) = 1) (B : Fin N → List (Fin k)) (hRowInt : TypeKernelIntegrable F)
    (hLeftDiff : LeftDifferentiation F w Xt) (hRightDiff : RightDifferentiation F w Xt hXt) (hTransfer : DerivativeTransfer F w Xt B)
    {c : (Fin N → ℝ) → ℝ} (hc : ContDiffOn ℝ (⊤ : ℕ∞) c (F.V : Set (Fin N → ℝ)))
    (hc0 : ∀ ξ ∈ (F.V : Set (Fin N → ℝ)), 0 < c ξ) (a : TestFunction F.V ℝ (⊤ : ℕ∞))
    (hParametrix : ∀ b : TestFunction F.V ℝ (⊤ : ℕ∞), SignedParametrixNoDrift F Xt c a b) (l : Fin k) :
    HasRepForm F Xt (repSumSquaresTest F Xt hXt) a [l] 0 1 := by
  obtain ⟨G, Cc, C0, h⟩ :=
    representation_typeOneForm_noDrift_of hXt hw B hRowInt hLeftDiff hRightDiff hTransfer hc hc0 a hParametrix
  refine ⟨fun _ => G l, fun K => match K with
    | [] => C0 l
    | [j] => Cc l j
    | _ => TypeOperator.zero F 1, fun u => ?_⟩
  refine repWeak_congr (h l u) (fun _ _ => rfl) (fun x _ => ?_)
  unfold RepForm
  rw [repWords_zero, Finset.sum_singleton, sum_repWords_succ, repWords_zero]
  simp only [Finset.sum_singleton, coe_repSumSquaresTest, wordDerivative]
  ring

/-- A word of length `m ≥ 1` has a type-1 form of level `(m - 1, m)`
(induction on the word by `hasRepForm_cons`, starting at `hasRepForm_one`). -/
theorem hasRepForm_length
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (F.V : Set (Fin N → ℝ)))
    (hw : ∀ j, (w j : ℕ) = 1) (B : Fin N → List (Fin k)) (hRowInt : TypeKernelIntegrable F)
    (hLeftDiff : LeftDifferentiation F w Xt) (hRightDiff : RightDifferentiation F w Xt hXt) (hTransfer : DerivativeTransfer F w Xt B)
    {c : (Fin N → ℝ) → ℝ} (hc : ContDiffOn ℝ (⊤ : ℕ∞) c (F.V : Set (Fin N → ℝ)))
    (hc0 : ∀ ξ ∈ (F.V : Set (Fin N → ℝ)), 0 < c ξ) (a : TestFunction F.V ℝ (⊤ : ℕ∞))
    (hParametrix : ∀ b : TestFunction F.V ℝ (⊤ : ℕ∞), SignedParametrixNoDrift F Xt c a b) :
    ∀ I : List (Fin k), 1 ≤ I.length →
      HasRepForm F Xt (repSumSquaresTest F Xt hXt) a I (I.length - 1) I.length
  | [], h => by simp at h
  | [l], _ => hasRepForm_one hXt hw B hRowInt hLeftDiff hRightDiff hTransfer hc hc0 a hParametrix l
  | i :: j :: I, _ => by
    have ih := hasRepForm_length hXt hw B hRowInt hLeftDiff hRightDiff hTransfer hc hc0 a hParametrix (j :: I) (by simp)
    have := hasRepForm_cons hXt hRowInt (repComm_of_transfer hXt hw B hRowInt hRightDiff hTransfer)
      (repSumSquaresTest F Xt hXt) ih i
    simpa using this

/-- Higher-order representation: without drift, for every word `I` of length `m ≥ 2` and every `a ∈ C_c^∞(V)`
there are endpoint type-0 families `S_IJ` (`|J| ≤ m - 2`) and `T_IK` (`|K| ≤ m - 1`), each an
endpoint operator (a finite sum of terms `X̃_j G`, `G` of type 1; here a single term `X̃_i G` with
`i` the first letter of `I`), with `X̃_I(a u) = ∑_J S_IJ X̃_J L̃u + ∑_K T_IK X̃_K u` for every test `u`
(weak derivative of the word `I` on `V`; the empty word is the identity). BB pp. 565–566, Thm 11.28.
Hypotheses: the exact statements `TypeKernelIntegrable`, `LeftDifferentiation`, `RightDifferentiation`, `DerivativeTransfer` of the
type calculus (for the no-drift commutation and left differentiation) and `SignedParametrixNoDrift` of
the left pair, with the standing density data. -/
theorem representation_higher_noDrift_of
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (F.V : Set (Fin N → ℝ)))
    (hw : ∀ j, (w j : ℕ) = 1) (B : Fin N → List (Fin k)) (hRowInt : TypeKernelIntegrable F)
    (hLeftDiff : LeftDifferentiation F w Xt) (hRightDiff : RightDifferentiation F w Xt hXt) (hTransfer : DerivativeTransfer F w Xt B)
    {c : (Fin N → ℝ) → ℝ} (hc : ContDiffOn ℝ (⊤ : ℕ∞) c (F.V : Set (Fin N → ℝ)))
    (hc0 : ∀ ξ ∈ (F.V : Set (Fin N → ℝ)), 0 < c ξ) (a : TestFunction F.V ℝ (⊤ : ℕ∞))
    (hParametrix : ∀ b : TestFunction F.V ℝ (⊤ : ℕ∞), SignedParametrixNoDrift F Xt c a b)
    (I : List (Fin k)) (hI : 2 ≤ I.length) :
    ∃ S T : List (Fin k) → TypeOperator F 0,
      (∀ J, IsEndpoint F Xt (S J)) ∧ (∀ K, IsEndpoint F Xt (T K)) ∧
      ∀ u : TestFunction F.V ℝ (⊤ : ℕ∞),
        hasWeakWordDeriv Xt F.V I (fun x => a x * u x)
          (fun ξ =>
            (∑ J ∈ repWords k (I.length - 2),
              (S J).apply (wordDerivative Xt J (sumSquares Xt (u : (Fin N → ℝ) → ℝ))) ξ) +
            ∑ K ∈ repWords k (I.length - 1),
              (T K).apply (wordDerivative Xt K (u : (Fin N → ℝ) → ℝ)) ξ) := by
  cases I with
  | nil => simp at hI
  | cons i I' =>
    have hI' : 1 ≤ I'.length := by simpa using hI
    obtain ⟨G, H, hGH⟩ := hasRepForm_length hXt hw B hRowInt hLeftDiff hRightDiff hTransfer hc hc0 a hParametrix I' hI'
    choose Sop hSop using fun T : TypeOperator F 1 =>
      exists_leftOp_of_eq (lam' := 0) hLeftDiff T i (by have := hw i; omega) (by have := hw i; omega)
    refine ⟨fun J => Sop (G J), fun K => Sop (H K), fun J => IsEndpoint.of_weakDeriv (hSop (G J)),
      fun K => IsEndpoint.of_weakDeriv (hSop (H K)), fun u => ?_⟩
    have h1 := repWeak_finset_sum hXt [i] (repWords k (I'.length - 1))
      (fun J ξ => (G J).apply (wordDerivative Xt J (repSumSquaresTest F Xt hXt u : (Fin N → ℝ) → ℝ)) ξ)
      (fun J ξ => (Sop (G J)).apply
        (wordDerivative Xt J (repSumSquaresTest F Xt hXt u : (Fin N → ℝ) → ℝ)) ξ)
      (fun J _ => hSop (G J) (S.wordDerivativeTest F.V Xt hXt J (repSumSquaresTest F Xt hXt u)))
    have h2 := repWeak_finset_sum hXt [i] (repWords k I'.length)
      (fun K ξ => (H K).apply (wordDerivative Xt K (u : (Fin N → ℝ) → ℝ)) ξ)
      (fun K ξ => (Sop (H K)).apply (wordDerivative Xt K (u : (Fin N → ℝ) → ℝ)) ξ)
      (fun K _ => hSop (H K) (S.wordDerivativeTest F.V Xt hXt K u))
    have h3 := (S.hasWeakWordDeriv_cons_iff Xt F.V hXt (hGH u) i).mpr
      (S.hasWeakWordDeriv_add Xt F.V hXt h1 h2)
    simp only [List.length_cons, coe_repSumSquaresTest] at h3 ⊢
    exact h3

end RothschildStein.P1
