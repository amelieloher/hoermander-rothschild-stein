-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ContinuityTheorem
public import RothschildStein.P1.TypeCalculusStatements
public import RothschildStein.P1.TypeClosure
public import RothschildStein.S.WeakDeriv
public import RothschildStein.S.Sobolev

/-!
# Gain: iterated left differentiation and local integrability

Under the exact statement `LeftDifferentiation` (left differentiation of types: for type `λ ≥ w_i`, the weak
`X̃ᵢ`-derivative of `T f` on tests is `S f` with `S` of type `λ - w_i`), iterating along a word `I`
whose weight is at most `λ` gives an operator `S_I` of type `λ - |I|` whose action on tests is the weak
`X̃_I`-derivative of `T f` (`LeftDifferentiation.exists_wordOperator`): `X̃_{i :: I'} = X̃_i X̃_{I'}`, and the weak
derivative of a weak derivative is the cons word (`S.hasWeakWordDeriv_cons_iff`). The empty word needs
`T f` locally integrable on `V`, which follows from the continuity theorem (a test is of finite Hölder norm, so `T f ∈ C^α(V)` is
continuous on `V`: `TypeOperator.continuousOn_apply_holder`).
(BB pp. 567–568, Prop 11.30; proof of the gain theorem: "`P, X̃ᵢP` have positive types, and
`X̃ᵢX̃ⱼP, X̃₀P` type 0... Apply the continuity theorem and pass derivative identities from tests".)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal Topology
namespace RothschildStein.P1

section Word

variable {N k : ℕ} {F : KernelFrame N} {w : Fin k → ℕ+}
  {Xt : Fin k → (Fin N → ℝ) → (Fin N → ℝ)}

/-- **Iterated left differentiation** (`LeftDifferentiation`): for a type-`λ` operator `T` with `T f`
locally integrable on `V` for tests `f`, and every word `I` of weight at most `λ`, there is an
operator `S` of type `λ - |I|` whose action on tests is the weak `X̃_I`-derivative of `T f` on `V`
(`hasWeakWordDeriv`). -/
theorem LeftDifferentiation.exists_wordOperator (hLeftDiff : LeftDifferentiation F w Xt)
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (F.V : Set (Fin N → ℝ))) {lam : ℕ}
    (T : TypeOperator F lam)
    (hloc : ∀ f : TestFunction F.V ℝ (⊤ : ℕ∞),
      LocallyIntegrableOn (T.apply f) (F.V : Set (Fin N → ℝ)) volume) :
    ∀ I : List (Fin k), wordWeight w I ≤ lam →
      ∃ S : TypeOperator F (lam - wordWeight w I), ∀ f : TestFunction F.V ℝ (⊤ : ℕ∞),
        hasWeakWordDeriv Xt F.V I (T.apply f) (S.apply f) := by
  intro I
  induction I with
  | nil =>
    intro _
    have hw0 : lam = lam - wordWeight w ([] : List (Fin k)) := by simp [wordWeight]
    refine ⟨T.ofEq hw0, fun f => ?_⟩
    have he : (T.ofEq hw0).apply f = T.apply f := funext fun ξ => TypeOperator.apply_ofEq hw0 T f ξ
    rw [he]
    exact S.hasWeakWordDeriv_nil Xt F.V (hloc f)
  | cons i I ih =>
    intro hI
    have hwi : wordWeight w (i :: I) = (w i : ℕ) + wordWeight w I := by simp [wordWeight]
    obtain ⟨S', hS'⟩ := ih (by omega)
    obtain ⟨S'', hS''⟩ := hLeftDiff (lam - wordWeight w I) S' i (by omega)
    have heq : lam - wordWeight w I - (w i : ℕ) = lam - wordWeight w (i :: I) := by omega
    refine ⟨S''.ofEq heq, fun f => ?_⟩
    have he : (S''.ofEq heq).apply f = S''.apply f :=
      funext fun ξ => TypeOperator.apply_ofEq heq S'' f ξ
    rw [he]
    exact (S.hasWeakWordDeriv_cons_iff Xt F.V hXt (hS' f) i).mpr (hS'' f)

end Word

namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}

/-- The lifted fields are smooth on the cutoff region of a lifted frame (`V ⊆ U`, `cl U` lies
in the lifted domain `O`). -/
theorem IsLiftedFrame.contDiffOn_Xl (hF : C.IsLiftedFrame F) (i : Fin k) :
    ContDiffOn ℝ (⊤ : ℕ∞) (C.Xl i) (F.V : Set (Fin (n + m) → ℝ)) :=
  (C.lift_smooth i).mono (hF.subset_U.trans (subset_closure.trans C.closure_U_subset))

variable {q : ℕ} {H : H1.StandingHypotheses C.G q} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)} {lam : ℕ}

/-- The action of a type-`λ` operator on a function of finite Hölder norm is continuous on
`V` (it has finite Hölder norm by the Hölder continuity of type operators). -/
theorem _root_.RothschildStein.P1.TypeOperator.continuousOn_apply_holder
    (hF : C.IsStandardFrame F H K hQ) (T : TypeOperator F lam) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {f : (Fin (n + m) → ℝ) → ℝ} (hf : holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) f ≠ ⊤) :
    ContinuousOn (T.apply f) (F.V : Set (Fin (n + m) → ℝ)) := by
  obtain ⟨CH, hCH, -, hb⟩ := T.exists_holderENorm_bound_standard hF hα0 hα1
  refine continuousOn_of_holderENorm_lt_top hF.lifted.subset_U hα0 ?_
  exact lt_of_le_of_lt (hb f) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.mpr hf))

/-- The action of a type-`λ` operator on a function of finite Hölder norm is locally
integrable on `V`. -/
theorem _root_.RothschildStein.P1.TypeOperator.locallyIntegrableOn_apply_holder
    (hF : C.IsStandardFrame F H K hQ) (T : TypeOperator F lam) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {f : (Fin (n + m) → ℝ) → ℝ} (hf : holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) f ≠ ⊤) :
    LocallyIntegrableOn (T.apply f) (F.V : Set (Fin (n + m) → ℝ)) volume :=
  (T.continuousOn_apply_holder hF hα0 hα1 hf).locallyIntegrableOn F.V.isOpen.measurableSet

/-- The action of a type-`λ` operator on a test function is locally integrable on `V`. -/
theorem _root_.RothschildStein.P1.TypeOperator.locallyIntegrableOn_apply_test
    (hF : C.IsStandardFrame F H K hQ) (T : TypeOperator F lam)
    (f : TestFunction F.V ℝ (⊤ : ℕ∞)) :
    LocallyIntegrableOn (T.apply f) (F.V : Set (Fin (n + m) → ℝ)) volume :=
  T.locallyIntegrableOn_apply_holder hF (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    (holderENorm_ne_top_of_contDiff_compact hF.lifted.subset_U f.contDiff f.hasCompactSupport
      (f.tsupport_subset.trans hF.lifted.subset_U) (by norm_num) (by norm_num))

/-- **The weak derivative along a word of a type-`λ` operator on tests, on a standard frame**
(`LeftDifferentiation` iterated): for every word `I` of weight at most `λ` there is an operator `S` of type
`λ - |I|` with `X̃_I (T f) = S f` weakly on `V`, for every test `f`. -/
theorem _root_.RothschildStein.P1.TypeOperator.exists_wordOperator_standard
    (hF : C.IsStandardFrame F H K hQ) (hLeftDiff : LeftDifferentiation F w C.Xl) (T : TypeOperator F lam)
    (I : List (Fin k)) (hI : wordWeight w I ≤ lam) :
    ∃ S : TypeOperator F (lam - wordWeight w I), ∀ f : TestFunction F.V ℝ (⊤ : ℕ∞),
      hasWeakWordDeriv C.Xl F.V I (T.apply f) (S.apply f) :=
  hLeftDiff.exists_wordOperator hF.lifted.contDiffOn_Xl T (T.locallyIntegrableOn_apply_test hF) I hI

end LiftedChart

end RothschildStein.P1
