-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.Commutation
public import RothschildStein.Definitions.sumSquaresWithDrift

/-!
# Lifted commutation formula for `L̃`

For the drift alphabet `Fin (q + 1)` (the drift `X̃₀` of weight two, the horizontal `X̃₁, …, X̃_q` of
weight one) and `L̃ = ∑_{k ≥ 1} X̃_k² + X̃₀` (that is, `sumSquaresWithDrift`), the commutation
`X̃ᵢ T = ∑_k F_ik X̃_k + F_i0 + P_i X̃₀` of `commutation_of_transfer` becomes
`X̃ᵢ T = ∑_k F̂_ik X̃_k + F_i0 + P_i L̃` (BB p. 560, Rem 11.20, (11.25)): replace
`X̃₀ = L̃ - ∑_k X̃_k²`; then `P_i X̃_k` has the type of `P_i` lowered by one (right differentiation,
`RightDifferentiation`), so the squared terms merge into the horizontal coefficients
`F̂_ik = F_ik - P_i X̃_k`, of the same type as `F_ik` (BB: `P_i X̃_k` has type `lam`,
`P_0 X̃_k` type `lam - 1`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped Topology
namespace RothschildStein.P1

variable {N q : ℕ} {F : KernelFrame N} {w : Fin (q + 1) → ℕ+}
  {Xt : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)}

/-- `L̃ f` is a test input for a test function `f`: continuous with compact support. -/
theorem isTestInput_sumSquaresWithDrift
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (F.V : Set (Fin N → ℝ)))
    (f : TestFunction F.V ℝ (⊤ : ℕ∞)) :
    IsTestInput (sumSquaresWithDrift Xt (f : (Fin N → ℝ) → ℝ)) := by
  have h : sumSquaresWithDrift Xt (f : (Fin N → ℝ) → ℝ) = fun η =>
      wordDerivative Xt [0] (f : (Fin N → ℝ) → ℝ) η +
        ∑ j : Fin q, wordDerivative Xt [j.succ, j.succ] (f : (Fin N → ℝ) → ℝ) η := rfl
  rw [h]
  exact (isTestInput_wordDerivative hXt [0] f).add
    (IsTestInput.sum _ fun j _ => isTestInput_wordDerivative hXt [j.succ, j.succ] f)

/-- The drift field's derivative is `L̃ f` minus the squares of the horizontal ones. -/
theorem fieldDerivative_drift_eq (f : (Fin N → ℝ) → ℝ) :
    fieldDerivative (Xt 0) f = fun η =>
      sumSquaresWithDrift Xt f η +
        (-1 : ℝ) * ∑ j : Fin q, wordDerivative Xt [j.succ, j.succ] f η := by
  funext η
  have h : sumSquaresWithDrift Xt f η = fieldDerivative (Xt 0) f η +
      ∑ j : Fin q, wordDerivative Xt [j.succ, j.succ] f η := rfl
  rw [h]
  ring

/-- Lifted `L̃`-version of the commutation (BB p. 560, Rem 11.20): for the
drift alphabet `Fin (q + 1)` (`w 0 = 2`, `w j.succ = 1`) and `T` of type `lam ≥ w i`,
`X̃ᵢ T = ∑_k F̂_ik X̃_k + F_i0 + P_i L̃` on tests (weak `X̃ᵢ`-derivative on `V`), with `F̂_ik, F_i0`
of type `lam + 1 - w i` and `P_i` of type `lam + 2 - w i`, assuming `TypeKernelIntegrable`,
`RightDifferentiation` and `DerivativeTransfer`. -/
theorem commutation_liftedL_of_transfer
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (F.V : Set (Fin N → ℝ)))
    (hw0 : (w 0 : ℕ) = 2) (hw : ∀ j : Fin q, (w j.succ : ℕ) = 1)
    (B : Fin N → List (Fin (q + 1)))
    (hRowInt : TypeKernelIntegrable F) (hRightDiff : RightDifferentiation F w Xt hXt) (hTransfer : DerivativeTransfer F w Xt B)
    {lam : ℕ} (T : TypeOperator F lam) (i : Fin (q + 1)) (hi : (w i : ℕ) ≤ lam) :
    ∃ (Fh : Fin q → TypeOperator F (lam + 1 - w i)) (F0 : TypeOperator F (lam + 1 - w i))
      (P : TypeOperator F (lam + 2 - w i)),
      ∀ f : TestFunction F.V ℝ (⊤ : ℕ∞),
        hasWeakWordDeriv Xt F.V [i] (T.apply f)
          (fun ξ =>
            (∑ j : Fin q, (Fh j).apply (fieldDerivative (Xt j.succ) (f : (Fin N → ℝ) → ℝ)) ξ) +
              F0.apply f ξ + P.apply (sumSquaresWithDrift Xt (f : (Fin N → ℝ) → ℝ)) ξ) := by
  have hw' : ∀ j, (w j : ℕ) = 1 ∨ (w j : ℕ) = 2 := fun j =>
    Fin.cases (Or.inr hw0) (fun j => Or.inl (hw j)) j
  obtain ⟨A, A₀, Bd, h⟩ := commutation_of_transfer hXt hw' B hRowInt hRightDiff hTransfer T i hi
  have hwi : 1 ≤ (w i : ℕ) := (w i).pos
  have hne : lam + 1 - (w i : ℕ) ≠ 0 := by omega
  have hf1 : ∀ g : Fin (q + 1) → ℝ,
      ∑ j ∈ Finset.univ.filter (fun j => (w j : ℕ) = 1), g j = ∑ j : Fin q, g j.succ := by
    intro g
    rw [Finset.sum_filter, Fin.sum_univ_succ]
    simp [hw0, hw]
  have hf2 : ∀ g : Fin (q + 1) → ℝ,
      ∑ j ∈ Finset.univ.filter (fun j => (w j : ℕ) = 2), g j = g 0 := by
    intro g
    rw [Finset.sum_filter, Fin.sum_univ_succ]
    simp [hw0, hw]
  choose Sq hSq using fun j : Fin q =>
    hRightDiff (lam + 2 - (w i : ℕ)) (Bd 0) j.succ (by have := hw j; omega)
  refine ⟨fun j => (A j.succ).add (((Sq j).ofEq (by have := hw j; omega)).neg), A₀, Bd 0,
    fun f => ?_⟩
  have hfun : (fun ξ =>
        (∑ j : Fin q,
            ((A j.succ).add (((Sq j).ofEq (by have := hw j; omega)).neg) :
              TypeOperator F (lam + 1 - w i)).apply
              (fieldDerivative (Xt j.succ) (f : (Fin N → ℝ) → ℝ)) ξ) +
          A₀.apply f ξ + (Bd 0).apply (sumSquaresWithDrift Xt (f : (Fin N → ℝ) → ℝ)) ξ) =
      fun ξ =>
        (∑ j ∈ Finset.univ.filter (fun j => (w j : ℕ) = 1),
            (A j).apply (fieldDerivative (Xt j) (f : (Fin N → ℝ) → ℝ)) ξ) +
          A₀.apply f ξ +
          ∑ j ∈ Finset.univ.filter (fun j => (w j : ℕ) = 2),
            (Bd j).apply (fieldDerivative (Xt j) (f : (Fin N → ℝ) → ℝ)) ξ := by
    funext ξ
    rw [hf1, hf2]
    -- `P_i X̃₀ f = P_i L̃ f - ∑_k P_i X̃_k X̃_k f`
    have hpos : lam + 2 - (w i : ℕ) ≠ 0 := by omega
    have hsq : ∀ j : Fin q, IsTestInput
        (wordDerivative Xt [j.succ, j.succ] (f : (Fin N → ℝ) → ℝ)) := fun j =>
      isTestInput_wordDerivative hXt [j.succ, j.succ] f
    have key : (Bd 0).apply (fieldDerivative (Xt 0) (f : (Fin N → ℝ) → ℝ)) ξ =
        (Bd 0).apply (sumSquaresWithDrift Xt (f : (Fin N → ℝ) → ℝ)) ξ -
          ∑ j : Fin q, (Sq j).apply (fieldDerivative (Xt j.succ) (f : (Fin N → ℝ) → ℝ)) ξ := by
      rw [fieldDerivative_drift_eq, TypeOperator.apply_add_input hRowInt hpos _
        (isTestInput_sumSquaresWithDrift hXt f)
        ((IsTestInput.sum _ fun j _ => hsq j).smul (-1)),
        TypeOperator.apply_smul_input hpos,
        TypeOperator.apply_sum_input hRowInt hpos _ _ fun j _ => hsq j]
      have hsum : ∑ j : Fin q, (Bd 0).apply
            (wordDerivative Xt [j.succ, j.succ] (f : (Fin N → ℝ) → ℝ)) ξ =
          ∑ j : Fin q, (Sq j).apply (fieldDerivative (Xt j.succ) (f : (Fin N → ℝ) → ℝ)) ξ :=
        Finset.sum_congr rfl fun j _ =>
          congrFun (hSq j (S.wordDerivativeTest F.V Xt hXt [j.succ] f)) ξ
      rw [hsum]
      ring
    have hFh : ∀ j : Fin q,
        ((A j.succ).add (((Sq j).ofEq (by have := hw j; omega)).neg) :
            TypeOperator F (lam + 1 - w i)).apply
          (fieldDerivative (Xt j.succ) (f : (Fin N → ℝ) → ℝ)) ξ =
        (A j.succ).apply (fieldDerivative (Xt j.succ) (f : (Fin N → ℝ) → ℝ)) ξ -
          (Sq j).apply (fieldDerivative (Xt j.succ) (f : (Fin N → ℝ) → ℝ)) ξ := by
      intro j
      rw [TypeOperator.apply_add hRowInt hne _ _ (isTestInput_fieldDerivative hXt j.succ f),
        TypeOperator.apply_neg hne, TypeOperator.apply_ofEq]
      ring
    rw [key, Finset.sum_congr rfl fun j _ => hFh j, Finset.sum_sub_distrib]
    ring
  exact (congrArg (hasWeakWordDeriv Xt F.V [i] (T.apply f)) hfun).mpr (h f)

/-- Horizontal `L̃`-version (BB p. 560): for `w i = 1` and `T` of type `lam ≥ 1`,
`X̃ᵢ T = ∑_k F̂_ik X̃_k + F_i0 + P_i L̃`, with `F̂_ik, F_i0` of type `lam` and `P_i` of type
`lam + 1`. -/
theorem horizontal_commutation_liftedL_of_transfer
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (F.V : Set (Fin N → ℝ)))
    (hw0 : (w 0 : ℕ) = 2) (hw : ∀ j : Fin q, (w j.succ : ℕ) = 1)
    (B : Fin N → List (Fin (q + 1)))
    (hRowInt : TypeKernelIntegrable F) (hRightDiff : RightDifferentiation F w Xt hXt) (hTransfer : DerivativeTransfer F w Xt B)
    {lam : ℕ} (hlam : 1 ≤ lam) (T : TypeOperator F lam) (i : Fin (q + 1)) (hi : (w i : ℕ) = 1) :
    ∃ (Fh : Fin q → TypeOperator F lam) (F0 : TypeOperator F lam)
      (P : TypeOperator F (lam + 1)),
      ∀ f : TestFunction F.V ℝ (⊤ : ℕ∞),
        hasWeakWordDeriv Xt F.V [i] (T.apply f)
          (fun ξ =>
            (∑ j : Fin q, (Fh j).apply (fieldDerivative (Xt j.succ) (f : (Fin N → ℝ) → ℝ)) ξ) +
              F0.apply f ξ + P.apply (sumSquaresWithDrift Xt (f : (Fin N → ℝ) → ℝ)) ξ) := by
  obtain ⟨Fh, F0, P, h⟩ :=
    commutation_liftedL_of_transfer hXt hw0 hw B hRowInt hRightDiff hTransfer T i (by omega)
  refine ⟨fun j => (Fh j).ofEq (by omega), F0.ofEq (by omega), P.ofEq (by omega), fun f => ?_⟩
  simpa only [TypeOperator.apply_ofEq] using h f

end RothschildStein.P1
