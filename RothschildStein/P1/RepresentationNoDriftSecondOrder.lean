-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.RepresentationNoDriftFirstOrder

/-!
# Second-order representation without drift: `X̃_m X̃_l(a u) = S_ml L̃u + ∑ₖ S_mlk X̃ₖu + S_ml0 u`

Without drift this is the case of two letters of the higher-order representation
(`representation_higher_noDrift_of`, BB pp. 565–566, Thm 11.28): for the word `I = m l` of length two the
families `S_IJ` (`|J| ≤ 0`) and `T_IK` (`|K| ≤ 1`) are `S_ml = S_I∅`, `S_ml0 = T_I∅` and
`S_mlk = T_I[k]` (the empty word is the identity), all endpoint operators of type 0 (BB p. 564, Thm
11.26, (11.42)–(11.44), without drift). This is the no-drift counterpart of
`representation_secondOrder_of`.
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

/-- Second-order representation without drift: for `a ∈ C_c^∞(V)` there are type-0 endpoint
operators `S_ml, S_mlk, S_ml0` with
`X̃_m X̃_l(a u) = S_ml L̃u + ∑ₖ S_mlk X̃ₖu + S_ml0 u` for every test `u` and generators `m, l`
(weak derivative on `V` of the word `m l`, `L̃ = sumSquares`; BB p. 564, Thm 11.26, (11.42)–(11.44),
without drift). Hypotheses: the exact statements `TypeKernelIntegrable`, `LeftDifferentiation`, `RightDifferentiation`,
`DerivativeTransfer` of the type calculus used by the commutation formula, and `SignedParametrixNoDrift` (with the density data
of its standing hypotheses). -/
theorem representation_secondOrder_noDrift_of
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (F.V : Set (Fin N → ℝ)))
    (hw : ∀ j, (w j : ℕ) = 1) (B : Fin N → List (Fin k)) (hRowInt : TypeKernelIntegrable F)
    (hLeftDiff : LeftDifferentiation F w Xt) (hRightDiff : RightDifferentiation F w Xt hXt) (hTransfer : DerivativeTransfer F w Xt B)
    {c : (Fin N → ℝ) → ℝ} (hc : ContDiffOn ℝ (⊤ : ℕ∞) c (F.V : Set (Fin N → ℝ)))
    (hc0 : ∀ ξ ∈ (F.V : Set (Fin N → ℝ)), 0 < c ξ) (a : TestFunction F.V ℝ (⊤ : ℕ∞))
    (hParametrix : ∀ b : TestFunction F.V ℝ (⊤ : ℕ∞), SignedParametrixNoDrift F Xt c a b) :
    ∃ (Sml : Fin k → Fin k → TypeOperator F 0)
      (Smlk : Fin k → Fin k → Fin k → TypeOperator F 0)
      (Sml0 : Fin k → Fin k → TypeOperator F 0),
      (∀ m l, IsEndpoint F Xt (Sml m l)) ∧ (∀ m l j, IsEndpoint F Xt (Smlk m l j)) ∧
      (∀ m l, IsEndpoint F Xt (Sml0 m l)) ∧
      ∀ (m l : Fin k) (u : TestFunction F.V ℝ (⊤ : ℕ∞)),
        hasWeakWordDeriv Xt F.V [m, l] (fun x => a x * u x)
          (fun ξ => (Sml m l).apply (sumSquares Xt u) ξ +
            (∑ j, (Smlk m l j).apply (fieldDerivative (Xt j) (u : (Fin N → ℝ) → ℝ)) ξ) +
            (Sml0 m l).apply u ξ) := by
  choose S T hS hT hrep using fun m l : Fin k =>
    representation_higher_noDrift_of hXt hw B hRowInt hLeftDiff hRightDiff hTransfer hc hc0 a hParametrix [m, l] (by simp)
  refine ⟨fun m l => S m l [], fun m l j => T m l [j], fun m l => T m l [],
    fun m l => hS m l [], fun m l j => hT m l [j], fun m l => hT m l [], fun m l u => ?_⟩
  refine repWeak_congr (hrep m l u) (fun _ _ => rfl) (fun x _ => ?_)
  simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceSub,
    repWords_zero, Finset.sum_singleton]
  rw [show (1 : ℕ) = 0 + 1 from rfl, sum_repWords_succ, repWords_zero]
  simp only [Finset.sum_singleton, wordDerivative]
  ring

end RothschildStein.P1
