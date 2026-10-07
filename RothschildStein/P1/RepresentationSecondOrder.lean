-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.RepresentationFirstOrder
public import RothschildStein.P1.CommutationLifted

/-!
# Second-order representation: `X̃_m X̃_l(a u) = S_ml L̃u + ∑ₖ S_mlk X̃ₖu + S_ml0 u`

Apply the `L̃`-version of the commutation formula (`horizontal_commutation_liftedL_of_transfer`) to the second term of
`X̃_l(a u) = X̃_l(P₂ L̃u) + X̃_l(F₂ u)`:
`X̃_l(a u) = (X̃_l P₂ + P_l) L̃u + ∑ₖ F̂_lk X̃ₖ u + F_l0 u`
with all coefficients of type 1 (`X̃_l P₂` type 1, `P_l` type 2 hence of type 1); this is
`representation_typeOneForm_of`. Differentiating by `X̃_m` (left differentiation, `LeftDifferentiation`) makes
every coefficient an endpoint operator of type 0 (a single term `X̃_m G`, `G` of type 1), without
reusing `F_l0` for two terms (BB p. 564, Thm 11.26, (11.42)–(11.44)). Hypotheses: the exact
statements `TypeKernelIntegrable`, `LeftDifferentiation`, `RightDifferentiation`, `DerivativeTransfer` of the type calculus used by the commutation formula,
and `SignedParametrix` (with the density data of its standing hypotheses).
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

/-- The intermediate type-1 form: for `a ∈ C_c^∞(V)` and horizontal `l ≥ 1`,
`X̃_l(a u) = G_l L̃u + ∑ₖ C_lk X̃ₖ u + C_l0 u` on tests `u` (weak derivative on `V`), all of `G_l, C_lk,
C_l0` of type 1 (`G_l = X̃_l P₂ + P_l` of types 1 and 2; BB p. 564, (11.42)). -/
theorem representation_typeOneForm_of
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (F.V : Set (Fin N → ℝ)))
    (hw0 : (w 0 : ℕ) = 2) (hw : ∀ j : Fin q, (w j.succ : ℕ) = 1)
    (B : Fin N → List (Fin (q + 1))) (hRowInt : TypeKernelIntegrable F) (hLeftDiff : LeftDifferentiation F w Xt)
    (hRightDiff : RightDifferentiation F w Xt hXt) (hTransfer : DerivativeTransfer F w Xt B)
    {c : (Fin N → ℝ) → ℝ} (hc : ContDiffOn ℝ (⊤ : ℕ∞) c (F.V : Set (Fin N → ℝ)))
    (hc0 : ∀ ξ ∈ (F.V : Set (Fin N → ℝ)), 0 < c ξ) (a : TestFunction F.V ℝ (⊤ : ℕ∞))
    (hParametrix : ∀ b : TestFunction F.V ℝ (⊤ : ℕ∞), SignedParametrix F Xt c a b) :
    ∃ (G : Fin q → TypeOperator F 1) (Cc : Fin q → Fin q → TypeOperator F 1)
      (C0 : Fin q → TypeOperator F 1),
      ∀ (l : Fin q) (u : TestFunction F.V ℝ (⊤ : ℕ∞)),
        hasWeakWordDeriv Xt F.V [l.succ] (fun x => a x * u x)
          (fun ξ => (G l).apply (sumSquaresWithDrift Xt u) ξ +
            (∑ j : Fin q, (Cc l j).apply (fieldDerivative (Xt j.succ) (u : (Fin N → ℝ) → ℝ)) ξ) +
            (C0 l).apply u ξ) := by
  obtain ⟨P₂, F₂, hzero⟩ := exists_zeroth_rep hc hc0 a hParametrix
  choose Ql hQl using fun l : Fin q =>
    exists_leftOp_of_eq (lam' := 1) hLeftDiff P₂ l.succ (by have := hw l; omega)
      (by have := hw l; omega)
  choose Fh F0 Pl hcomm using fun l : Fin q =>
    horizontal_commutation_liftedL_of_transfer hXt hw0 hw B hRowInt hRightDiff hTransfer (lam := 1) le_rfl F₂
      l.succ (hw l)
  refine ⟨fun l => (Ql l).add ((Pl l).mono (by norm_num : 1 ≤ 2)), Fh, F0, fun l u => ?_⟩
  have h1 := hQl l (sumSquaresWithDriftTest F.V Xt hXt u)
  rw [sumSquaresWithDriftTest_coe] at h1
  refine repWeak_congr (S.hasWeakWordDeriv_add Xt F.V hXt h1 (hcomm l u))
    (fun x hx => (hzero u x hx).symm) (fun x _ => ?_)
  have hadd := TypeOperator.apply_add hRowInt (by norm_num : (1 : ℕ) ≠ 0) (Ql l)
    ((Pl l).mono (by norm_num : 1 ≤ 2)) (isTestInput_sumSquaresWithDrift hXt u) x
  rw [hadd, TypeOperator.apply_mono_of_ne_zero (by norm_num) (Pl l) (by norm_num)]
  ring

/-- Second-order representation: for `a ∈ C_c^∞(V)` there are type-0 endpoint operators
`S_ml, S_mlk, S_ml0` (each a single term `X̃_m G` with `G` of type 1) with
`X̃_m X̃_l(a u) = S_ml L̃u + ∑ₖ S_mlk X̃ₖ u + S_ml0 u` for every test `u` and horizontal `m, l ≥ 1`
(weak derivative on `V` of the word `m l`; BB p. 564, Thm 11.26, (11.42)–(11.44)). -/
theorem representation_secondOrder_of
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (F.V : Set (Fin N → ℝ)))
    (hw0 : (w 0 : ℕ) = 2) (hw : ∀ j : Fin q, (w j.succ : ℕ) = 1)
    (B : Fin N → List (Fin (q + 1))) (hRowInt : TypeKernelIntegrable F) (hLeftDiff : LeftDifferentiation F w Xt)
    (hRightDiff : RightDifferentiation F w Xt hXt) (hTransfer : DerivativeTransfer F w Xt B)
    {c : (Fin N → ℝ) → ℝ} (hc : ContDiffOn ℝ (⊤ : ℕ∞) c (F.V : Set (Fin N → ℝ)))
    (hc0 : ∀ ξ ∈ (F.V : Set (Fin N → ℝ)), 0 < c ξ) (a : TestFunction F.V ℝ (⊤ : ℕ∞))
    (hParametrix : ∀ b : TestFunction F.V ℝ (⊤ : ℕ∞), SignedParametrix F Xt c a b) :
    ∃ (Sml : Fin q → Fin q → TypeOperator F 0)
      (Smlk : Fin q → Fin q → Fin q → TypeOperator F 0)
      (Sml0 : Fin q → Fin q → TypeOperator F 0),
      (∀ m l, IsEndpoint F Xt (Sml m l)) ∧ (∀ m l k, IsEndpoint F Xt (Smlk m l k)) ∧
      (∀ m l, IsEndpoint F Xt (Sml0 m l)) ∧
      ∀ (m l : Fin q) (u : TestFunction F.V ℝ (⊤ : ℕ∞)),
        hasWeakWordDeriv Xt F.V [m.succ, l.succ] (fun x => a x * u x)
          (fun ξ => (Sml m l).apply (sumSquaresWithDrift Xt u) ξ +
            (∑ k : Fin q, (Smlk m l k).apply (fieldDerivative (Xt k.succ) (u : (Fin N → ℝ) → ℝ)) ξ) +
            (Sml0 m l).apply u ξ) := by
  obtain ⟨G, Cc, C0, hform⟩ :=
    representation_typeOneForm_of hXt hw0 hw B hRowInt hLeftDiff hRightDiff hTransfer hc hc0 a hParametrix
  choose Sop hSop using fun (m : Fin q) (T : TypeOperator F 1) =>
    exists_leftOp_of_eq (lam' := 0) hLeftDiff T m.succ (by have := hw m; omega) (by have := hw m; omega)
  refine ⟨fun m l => Sop m (G l), fun m l k => Sop m (Cc l k), fun m l => Sop m (C0 l),
    fun m l => IsEndpoint.of_weakDeriv (hSop m (G l)),
    fun m l k => IsEndpoint.of_weakDeriv (hSop m (Cc l k)),
    fun m l => IsEndpoint.of_weakDeriv (hSop m (C0 l)), fun m l u => ?_⟩
  have h1 := hSop m (G l) (sumSquaresWithDriftTest F.V Xt hXt u)
  rw [sumSquaresWithDriftTest_coe] at h1
  have h2 := repWeak_finset_sum hXt [m.succ] (Finset.univ : Finset (Fin q))
    (fun j ξ => (Cc l j).apply (fieldDerivative (Xt j.succ) (u : (Fin N → ℝ) → ℝ)) ξ)
    (fun j ξ => (Sop m (Cc l j)).apply (fieldDerivative (Xt j.succ) (u : (Fin N → ℝ) → ℝ)) ξ)
    (fun j _ => hSop m (Cc l j) (S.wordDerivativeTest F.V Xt hXt [j.succ] u))
  exact (S.hasWeakWordDeriv_cons_iff Xt F.V hXt (hform l u) m.succ).mpr
    (repWeak_add₃ hXt h1 h2 (hSop m (C0 l) u))

end RothschildStein.P1
