-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.CommutationRight

/-!
# Commuting a generator with a type-`lam` operator

Let `T` be an operator of type `lam ≥ w i` and every generator have weight one (horizontal) or two
(drift). Then the weak `X̃ᵢ`-derivative of `T f` on `V` is
`∑_{w j = 1} A_j (X̃_j f) + A₀ f + ∑_{w j = 2} B_j (X̃_j f)` with `A_j, A₀` of type
`lam + 1 - w i` and `B_j` of type `lam + 2 - w i` (BB pp. 552, 559–560, Thm 11.19, (11.22)–(11.25)).

The proof expands every bracket into ordered words. The transfer to the integration variable
rewrites `X̃ᵢ T` as `∑_J T_J X̃_[J] + T⁰` (`DerivativeTransfer`); each bracket `X̃_[J]` expands into ordered words of weight
`|J|` (`fieldDerivative_wordBracket_test`); the prefix of each word is composed on the right of
`T_J` by iterated right differentiation (`RightDifferentiation`, `RightForm.of_word`), leaving an operator of
type `lam + w r - w i` against the rightmost letter `r`; finite sums collect the operators
(`RightForm.sum`, `RightForm.listSum`), by weight of `r`. Positive-type operators act linearly on
the bounded compactly supported inputs involved (`TypeKernelIntegrable`).
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

/-- Commutation (BB Thm 11.19, pp. 552, 559–560). Assume the row integrability
(`TypeKernelIntegrable`), right differentiation (`RightDifferentiation`) and transfer (`DerivativeTransfer`) statements
of the type calculus. For `T` of type `lam ≥ w i`, `X̃ᵢ T = ∑_{w j = 1} A_j X̃_j + A₀ +
∑_{w j = 2} B_j X̃_j` on tests, in the sense of the weak `X̃ᵢ`-derivative on `V`, with `A_j, A₀`
of type `lam + 1 - w i` and `B_j` of type `lam + 2 - w i`. -/
theorem commutation_of_transfer
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (F.V : Set (Fin N → ℝ)))
    (hw : ∀ j, (w j : ℕ) = 1 ∨ (w j : ℕ) = 2) (B : Fin N → List (Fin k))
    (hRowInt : TypeKernelIntegrable F) (hRightDiff : RightDifferentiation F w Xt hXt) (hTransfer : DerivativeTransfer F w Xt B)
    {lam : ℕ} (T : TypeOperator F lam) (i : Fin k) (hi : (w i : ℕ) ≤ lam) :
    ∃ (A : Fin k → TypeOperator F (lam + 1 - w i)) (A₀ : TypeOperator F (lam + 1 - w i))
      (Bd : Fin k → TypeOperator F (lam + 2 - w i)),
      ∀ f : TestFunction F.V ℝ (⊤ : ℕ∞),
        hasWeakWordDeriv Xt F.V [i] (T.apply f)
          (fun ξ =>
            (∑ j ∈ Finset.univ.filter (fun j => (w j : ℕ) = 1),
                (A j).apply (fieldDerivative (Xt j) (f : (Fin N → ℝ) → ℝ)) ξ) +
              A₀.apply f ξ +
              ∑ j ∈ Finset.univ.filter (fun j => (w j : ℕ) = 2),
                (Bd j).apply (fieldDerivative (Xt j) (f : (Fin N → ℝ) → ℝ)) ξ) := by
  obtain ⟨TJ, T0, hTJ⟩ := hTransfer lam T i hi
  have hwi : 1 ≤ (w i : ℕ) := (w i).pos
  -- the transferred part `∑_J T_J X̃_[J]` is a right form of base type `lam - w i`
  have hRF : RightForm F w Xt (lam - w i)
      (fun f ξ => ∑ j ∈ Finset.univ.filter (fun j => (w i : ℕ) ≤ wordWeight w (B j)),
        (TJ j).apply (fieldDerivative (wordBracket Xt (B j)) (f : (Fin N → ℝ) → ℝ)) ξ) := by
    refine RightForm.sum hXt hRowInt _ (Φ := fun j f ξ =>
      (TJ j).apply (fieldDerivative (wordBracket Xt (B j)) (f : (Fin N → ℝ) → ℝ)) ξ) ?_
    intro j hj
    have hj' : (w i : ℕ) ≤ wordWeight w (B j) := (Finset.mem_filter.1 hj).2
    have hpos : lam + wordWeight w (B j) - (w i : ℕ) ≠ 0 := by omega
    refine RightForm.congr (fun f ξ => ?_)
      (RightForm.listSum hXt hRowInt (bracketWords (B j)) (fun p => (p.1 : ℝ))
        (Φ := fun p f ξ => (TJ j).apply (wordDerivative Xt p.2 (f : (Fin N → ℝ) → ℝ)) ξ)
        fun p hp => ?_)
    · rw [fieldDerivative_wordBracket_test F.V Xt hXt (B j) f]
      exact TypeOperator.apply_listSum_input hRowInt hpos (TJ j) (bracketWords (B j))
        (fun p => (p.1 : ℝ)) (fun p _ => isTestInput_wordDerivative hXt p.2 f) ξ
    · exact RightForm.of_word hXt hRightDiff p.2 (ne_nil_of_mem_bracketWords hp)
        (by rw [wordWeight_of_mem_bracketWords hp]; omega) (TJ j)
  obtain ⟨C, hC⟩ := hRF
  refine ⟨fun j => ((C j).ofWeight w 1).ofEq (by omega), T0,
    fun j => ((C j).ofWeight w 2).ofEq (by omega), fun f => ?_⟩
  have hfun : (fun ξ =>
        (∑ j ∈ Finset.univ.filter (fun j => (w j : ℕ) = 1),
            (((C j).ofWeight w 1).ofEq (by omega) : TypeOperator F (lam + 1 - w i)).apply
              (fieldDerivative (Xt j) (f : (Fin N → ℝ) → ℝ)) ξ) +
          T0.apply f ξ +
          ∑ j ∈ Finset.univ.filter (fun j => (w j : ℕ) = 2),
            (((C j).ofWeight w 2).ofEq (by omega) : TypeOperator F (lam + 2 - w i)).apply
              (fieldDerivative (Xt j) (f : (Fin N → ℝ) → ℝ)) ξ) =
      fun ξ => (∑ j ∈ Finset.univ.filter (fun j => (w i : ℕ) ≤ wordWeight w (B j)),
          (TJ j).apply (fieldDerivative (wordBracket Xt (B j)) (f : (Fin N → ℝ) → ℝ)) ξ) +
        T0.apply f ξ := by
    funext ξ
    have hCf := hC f ξ
    beta_reduce at hCf
    rw [hCf, sum_split_weights hw]
    have h1 : ∑ j ∈ Finset.univ.filter (fun j => (w j : ℕ) = 1),
        (((C j).ofWeight w 1).ofEq (by omega) : TypeOperator F (lam + 1 - w i)).apply
          (fieldDerivative (Xt j) (f : (Fin N → ℝ) → ℝ)) ξ =
        ∑ j ∈ Finset.univ.filter (fun j => (w j : ℕ) = 1),
          (C j).apply (fieldDerivative (Xt j) (f : (Fin N → ℝ) → ℝ)) ξ := by
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [TypeOperator.apply_ofEq, TypeOperator.apply_ofWeight w 1 _ (Finset.mem_filter.1 hj).2]
    have h2 : ∑ j ∈ Finset.univ.filter (fun j => (w j : ℕ) = 2),
        (((C j).ofWeight w 2).ofEq (by omega) : TypeOperator F (lam + 2 - w i)).apply
          (fieldDerivative (Xt j) (f : (Fin N → ℝ) → ℝ)) ξ =
        ∑ j ∈ Finset.univ.filter (fun j => (w j : ℕ) = 2),
          (C j).apply (fieldDerivative (Xt j) (f : (Fin N → ℝ) → ℝ)) ξ := by
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [TypeOperator.apply_ofEq, TypeOperator.apply_ofWeight w 2 _ (Finset.mem_filter.1 hj).2]
    rw [h1, h2]
    ring
  exact (congrArg (hasWeakWordDeriv Xt F.V [i] (T.apply f)) hfun).mpr (hTJ f)

/-- Horizontal commutation (BB Thm 11.19, p. 552): for a horizontal generator `i`
(`w i = 1`) and `T` of type `lam ≥ 1`, `X̃ᵢ T = ∑_{w j = 1} F_ij X̃_j + F_i0 + ∑_{w j = 2} P_ij X̃_j`
on tests, with `F_ij, F_i0` of type `lam` and `P_ij` (the drift generator's) of type `lam + 1`. -/
theorem horizontal_commutation_of_transfer
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (F.V : Set (Fin N → ℝ)))
    (hw : ∀ j, (w j : ℕ) = 1 ∨ (w j : ℕ) = 2) (B : Fin N → List (Fin k))
    (hRowInt : TypeKernelIntegrable F) (hRightDiff : RightDifferentiation F w Xt hXt) (hTransfer : DerivativeTransfer F w Xt B)
    {lam : ℕ} (hlam : 1 ≤ lam) (T : TypeOperator F lam) (i : Fin k) (hi : (w i : ℕ) = 1) :
    ∃ (Fh : Fin k → TypeOperator F lam) (F0 : TypeOperator F lam)
      (P : Fin k → TypeOperator F (lam + 1)),
      ∀ f : TestFunction F.V ℝ (⊤ : ℕ∞),
        hasWeakWordDeriv Xt F.V [i] (T.apply f)
          (fun ξ =>
            (∑ j ∈ Finset.univ.filter (fun j => (w j : ℕ) = 1),
                (Fh j).apply (fieldDerivative (Xt j) (f : (Fin N → ℝ) → ℝ)) ξ) +
              F0.apply f ξ +
              ∑ j ∈ Finset.univ.filter (fun j => (w j : ℕ) = 2),
                (P j).apply (fieldDerivative (Xt j) (f : (Fin N → ℝ) → ℝ)) ξ) := by
  obtain ⟨A, A₀, Bd, h⟩ := commutation_of_transfer hXt hw B hRowInt hRightDiff hTransfer T i (by omega)
  refine ⟨fun j => (A j).ofEq (by omega), A₀.ofEq (by omega), fun j => (Bd j).ofEq (by omega),
    fun f => ?_⟩
  simpa only [TypeOperator.apply_ofEq] using h f

/-- Commutation without drift (BB Thm 11.19): all generators have weight
one, and `X̃ᵢ T = ∑_j F_ij X̃_j + F_i0` on tests, with `F_ij, F_i0` of type `lam`. -/
theorem noDrift_commutation_of_transfer
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (F.V : Set (Fin N → ℝ)))
    (hw : ∀ j, (w j : ℕ) = 1) (B : Fin N → List (Fin k))
    (hRowInt : TypeKernelIntegrable F) (hRightDiff : RightDifferentiation F w Xt hXt) (hTransfer : DerivativeTransfer F w Xt B)
    {lam : ℕ} (hlam : 1 ≤ lam) (T : TypeOperator F lam) (i : Fin k) :
    ∃ (Fh : Fin k → TypeOperator F lam) (F0 : TypeOperator F lam),
      ∀ f : TestFunction F.V ℝ (⊤ : ℕ∞),
        hasWeakWordDeriv Xt F.V [i] (T.apply f)
          (fun ξ =>
            (∑ j, (Fh j).apply (fieldDerivative (Xt j) (f : (Fin N → ℝ) → ℝ)) ξ) +
              F0.apply f ξ) := by
  obtain ⟨Fh, F0, P, h⟩ := horizontal_commutation_of_transfer hXt (fun j => Or.inl (hw j)) B
    hRowInt hRightDiff hTransfer hlam T i (hw i)
  refine ⟨Fh, F0, fun f => ?_⟩
  have h1 : Finset.univ.filter (fun j => (w j : ℕ) = 1) = Finset.univ :=
    Finset.filter_true_of_mem fun j _ => hw j
  have h2 : Finset.univ.filter (fun j => (w j : ℕ) = 2) = ∅ :=
    Finset.filter_false_of_mem fun j _ => by rw [hw j]; omega
  have := h f
  rw [h1, h2] at this
  simpa using this

end RothschildStein.P1
