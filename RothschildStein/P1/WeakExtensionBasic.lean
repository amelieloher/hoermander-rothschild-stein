-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.WeakExtensionParametrix
public import RothschildStein.P1.RepresentationSecondOrder

/-!
# First-order, second-order and drift representations on `W^{2,p}_{X̃,0}(V)`

The first-order, second-order and drift representations (BB pp. 564–565, Thm 11.26, Cor 11.27), proved on tests, extend to
`u ∈ W^{2,p}_{X̃,0}(V)` (`memSobolevXZero`, closure of the tests in the `W^{2,p}_{X̃}`
norm, `1 < p < ∞`) and are identities between weak derivatives (distributions) whose right-hand sides
are the bounded `L^p` extensions `T̄` of the type operators applied to the weak jet of `u` (the
indicated `L^p` representatives of the continuity theorem):

* `weakExtension_firstOrder`: `X̃_l(a u) = F̄_l L̃u + S̄_l u`;
* `weakExtension_secondOrder`: `X̃_i X̃_l(a u) = S̄_il L̃u + ∑ₖ S̄_ilk X̃ₖu + S̄_il0 u`;
* `weakExtension_drift`: `X̃₀(a u) = S̄⁽⁰⁾ L̃u + ∑ₖ S̄⁽⁰⁾ₖ X̃ₖu + S̄⁽⁰⁾₀ u` (coefficients smooth multipliers
  plus finite sums of endpoint operators).

Here `L̃u = D [0] + ∑ᵢ D [i, i]` and `X̃ₖu = D [k]` are the weak derivatives of the jet `D` of `u`
(`IsWeakJet`); the `_of` forms take exactly the hypotheses of `representation_firstOrder_of`,
`representation_secondOrder_of`, `representation_drift_of` (the exact statements `TypeKernelIntegrable`,
`LeftDifferentiation`, `RightDifferentiation`, `DerivativeTransfer`, `SignedParametrix`) and return the operators with both the identity
on tests and its extension. No regularity is asserted for an arbitrary distribution.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal Topology
namespace RothschildStein.P1

namespace LiftedChart

variable {n q : ℕ} {w : Fin (q + 1) → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}
  {r : ℕ} {H : H1.StandingHypotheses C.G r} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)} {P : ℝ≥0∞} [Fact (1 ≤ P)]

/-- **First-order representation, on `W^{2,P}_{X̃,0}(V)`**: if `X̃_l(a φ) = F_l L̃φ + S_l φ` weakly on
`V` for tests `φ` and horizontal `l ≥ 1`, then `X̃_l(a u) = F̄_l (L̃u) + S̄_l u` weakly on `V` for every
`u ∈ W^{2,P}_{X̃,0}(V)` with weak jet `D` (`L̃u = D [0] + ∑ᵢ D [i, i]`), `1 < P < ∞`. -/
theorem weakExtension_firstOrder (hF : C.IsStandardFrame F H K hQ)
    (hw0 : (w 0 : ℕ) = 2) (hw : ∀ j : Fin q, (w j.succ : ℕ) = 1)
    {a : TestFunction F.V ℝ (⊤ : ℕ∞)} {Fl : Fin q → TypeOperator F 1}
    {Sl : Fin q → TypeOperator F 0}
    (hid : ∀ (l : Fin q) (u : TestFunction F.V ℝ (⊤ : ℕ∞)),
      hasWeakWordDeriv C.Xl F.V [l.succ] (fun x => a x * u x)
        (fun ξ => (Fl l).apply (sumSquaresWithDrift C.Xl u) ξ + (Sl l).apply u ξ))
    (hP1 : 1 < P) (hP : P ≠ ⊤) {u : (Fin (n + m) → ℝ) → ℝ}
    (hu : memSobolevXZero w C.Xl F.V 2 P u) {D : List (Fin (q + 1)) → (Fin (n + m) → ℝ) → ℝ}
    (hD : IsWeakJet w C.Xl F.V 2 P u D) (l : Fin q) :
    hasWeakWordDeriv C.Xl F.V [l.succ] (fun x => a x * u x)
      (fun ξ => (Fl l).lpAct hF hP1 hP (weakSumSquaresWithDrift D) ξ +
        (Sl l).lpAct hF hP1 hP u ξ) := by
  refine weakExtension_mul hF.lifted.contDiffOn_Xl hF.lifted.volume_lt_top hu hD a [l.succ]
    (fun f ξ => (Fl l).apply (sumSquaresWithDrift C.Xl f) ξ + (Sl l).apply f ξ) _
    (fun φ hφ => ?_) (hid l)
  have h1 := (Fl l).convLp_apply hF hP1 hP
    (hφ.convLp_sumSquaresWithDrift hF.lifted.contDiffOn_Xl hw0 hw)
  simp only [sumSquaresWithDriftTest_coe] at h1
  exact h1.add ((Sl l).convLp_apply hF hP1 hP (hφ.convLp_nil hD))

/-- **Second-order representation, on `W^{2,P}_{X̃,0}(V)`**: if
`X̃_i X̃_l(a φ) = S_il L̃φ + ∑ₖ S_ilk X̃ₖφ + S_il0 φ` weakly on `V` for tests `φ` and horizontal
`i, l ≥ 1`, then the same identity holds with the bounded extensions `S̄` for every
`u ∈ W^{2,P}_{X̃,0}(V)` with weak jet `D` (`X̃ₖu = D [k]`). -/
theorem weakExtension_secondOrder (hF : C.IsStandardFrame F H K hQ)
    (hw0 : (w 0 : ℕ) = 2) (hw : ∀ j : Fin q, (w j.succ : ℕ) = 1)
    {a : TestFunction F.V ℝ (⊤ : ℕ∞)} {Sml : Fin q → Fin q → TypeOperator F 0}
    {Smlk : Fin q → Fin q → Fin q → TypeOperator F 0} {Sml0 : Fin q → Fin q → TypeOperator F 0}
    (hid : ∀ (i l : Fin q) (u : TestFunction F.V ℝ (⊤ : ℕ∞)),
      hasWeakWordDeriv C.Xl F.V [i.succ, l.succ] (fun x => a x * u x)
        (fun ξ => (Sml i l).apply (sumSquaresWithDrift C.Xl u) ξ +
          (∑ k : Fin q, (Smlk i l k).apply
            (fieldDerivative (C.Xl k.succ) (u : (Fin (n + m) → ℝ) → ℝ)) ξ) +
          (Sml0 i l).apply u ξ))
    (hP1 : 1 < P) (hP : P ≠ ⊤) {u : (Fin (n + m) → ℝ) → ℝ}
    (hu : memSobolevXZero w C.Xl F.V 2 P u) {D : List (Fin (q + 1)) → (Fin (n + m) → ℝ) → ℝ}
    (hD : IsWeakJet w C.Xl F.V 2 P u D) (i l : Fin q) :
    hasWeakWordDeriv C.Xl F.V [i.succ, l.succ] (fun x => a x * u x)
      (fun ξ => (Sml i l).lpAct hF hP1 hP (weakSumSquaresWithDrift D) ξ +
        (∑ k : Fin q, (Smlk i l k).lpAct hF hP1 hP (D [k.succ]) ξ) +
        (Sml0 i l).lpAct hF hP1 hP u ξ) := by
  have hXt := hF.lifted.contDiffOn_Xl
  refine weakExtension_mul hXt hF.lifted.volume_lt_top hu hD a [i.succ, l.succ]
    (fun f ξ => (Sml i l).apply (sumSquaresWithDrift C.Xl f) ξ +
      (∑ k : Fin q, (Smlk i l k).apply
        (fieldDerivative (C.Xl k.succ) (f : (Fin (n + m) → ℝ) → ℝ)) ξ) +
      (Sml0 i l).apply f ξ) _ (fun φ hφ => ?_) (hid i l)
  have h1 := (Sml i l).convLp_apply hF hP1 hP (hφ.convLp_sumSquaresWithDrift hXt hw0 hw)
  simp only [sumSquaresWithDriftTest_coe] at h1
  have h2 : ConvLp F.V P (fun j ξ => ∑ k : Fin q, (Smlk i l k).apply
      (fieldDerivative (C.Xl k.succ) (φ j : (Fin (n + m) → ℝ) → ℝ)) ξ)
      (fun ξ => ∑ k : Fin q, (Smlk i l k).lpAct hF hP1 hP (D [k.succ]) ξ) :=
    ConvLp.finset_sum Finset.univ fun k _ => (Smlk i l k).convLp_apply hF hP1 hP
      (ψ := fun j => S.wordDerivativeTest F.V C.Xl hXt [k.succ] (φ j))
      (hφ [k.succ] ((S.mem_wordFamily_iff w 2 _).2 (by simp [wordWeight, hw k])))
  exact (h1.add h2).add ((Sml0 i l).convLp_apply hF hP1 hP (hφ.convLp_nil hD))

/-- **First-order representation: representation and extension.** Under the hypotheses of
`representation_firstOrder_of`, there are type-1 `F_l` and endpoint type-0 `S_l` with
`X̃_l(a u) = F_l L̃u + S_l u` for tests `u`, and for every `1 < P < ∞` and `u ∈ W^{2,P}_{X̃,0}(V)` with
weak jet `D`, `X̃_l(a u) = F̄_l L̃u + S̄_l u` in distributions with the `L^P` representatives of the continuity theorem. -/
theorem weakExtension_firstOrder_of (hF : C.IsStandardFrame F H K hQ)
    (hw0 : (w 0 : ℕ) = 2) (hw : ∀ j : Fin q, (w j.succ : ℕ) = 1) (hLeftDiff : LeftDifferentiation F w C.Xl)
    {c : (Fin (n + m) → ℝ) → ℝ} (hc : ContDiffOn ℝ (⊤ : ℕ∞) c (F.V : Set (Fin (n + m) → ℝ)))
    (hc0 : ∀ ξ ∈ (F.V : Set (Fin (n + m) → ℝ)), 0 < c ξ) (a : TestFunction F.V ℝ (⊤ : ℕ∞))
    (hParametrix : ∀ b : TestFunction F.V ℝ (⊤ : ℕ∞), SignedParametrix F C.Xl c a b) :
    ∃ (Fl : Fin q → TypeOperator F 1) (Sl : Fin q → TypeOperator F 0),
      (∀ l, IsEndpoint F C.Xl (Sl l)) ∧
      (∀ (l : Fin q) (u : TestFunction F.V ℝ (⊤ : ℕ∞)),
        hasWeakWordDeriv C.Xl F.V [l.succ] (fun x => a x * u x)
          (fun ξ => (Fl l).apply (sumSquaresWithDrift C.Xl u) ξ + (Sl l).apply u ξ)) ∧
      (∀ (P : ℝ≥0∞) [Fact (1 ≤ P)] (hP1 : 1 < P) (hP : P ≠ ⊤) (u : (Fin (n + m) → ℝ) → ℝ)
          (D : List (Fin (q + 1)) → (Fin (n + m) → ℝ) → ℝ),
        memSobolevXZero w C.Xl F.V 2 P u → IsWeakJet w C.Xl F.V 2 P u D → ∀ l : Fin q,
        hasWeakWordDeriv C.Xl F.V [l.succ] (fun x => a x * u x)
          (fun ξ => (Fl l).lpAct hF hP1 hP (weakSumSquaresWithDrift D) ξ +
            (Sl l).lpAct hF hP1 hP u ξ)) := by
  obtain ⟨Fl, Sl, hend, hid⟩ :=
    representation_firstOrder_of hF.lifted.contDiffOn_Xl hw hLeftDiff hc hc0 a hParametrix
  exact ⟨Fl, Sl, hend, hid, fun P _ hP1 hP u D hu hD l =>
    weakExtension_firstOrder hF hw0 hw hid hP1 hP hu hD l⟩

/-- **Second-order representation: representation and extension.** Under the hypotheses of
`representation_secondOrder_of`, the type-0 endpoint operators `S_il, S_ilk, S_il0` satisfy
`X̃_i X̃_l(a u) = S_il L̃u + ∑ₖ S_ilk X̃ₖu + S_il0 u` for tests `u`, and the same identity with the
bounded extensions for every `u ∈ W^{2,P}_{X̃,0}(V)`, `1 < P < ∞`. -/
theorem weakExtension_secondOrder_of (hF : C.IsStandardFrame F H K hQ)
    (hw0 : (w 0 : ℕ) = 2) (hw : ∀ j : Fin q, (w j.succ : ℕ) = 1)
    (B : Fin (n + m) → List (Fin (q + 1))) (hRowInt : TypeKernelIntegrable F) (hLeftDiff : LeftDifferentiation F w C.Xl)
    (hRightDiff : RightDifferentiation F w C.Xl hF.lifted.contDiffOn_Xl) (hTransfer : DerivativeTransfer F w C.Xl B)
    {c : (Fin (n + m) → ℝ) → ℝ} (hc : ContDiffOn ℝ (⊤ : ℕ∞) c (F.V : Set (Fin (n + m) → ℝ)))
    (hc0 : ∀ ξ ∈ (F.V : Set (Fin (n + m) → ℝ)), 0 < c ξ) (a : TestFunction F.V ℝ (⊤ : ℕ∞))
    (hParametrix : ∀ b : TestFunction F.V ℝ (⊤ : ℕ∞), SignedParametrix F C.Xl c a b) :
    ∃ (Sml : Fin q → Fin q → TypeOperator F 0)
      (Smlk : Fin q → Fin q → Fin q → TypeOperator F 0)
      (Sml0 : Fin q → Fin q → TypeOperator F 0),
      (∀ i l, IsEndpoint F C.Xl (Sml i l)) ∧ (∀ i l k, IsEndpoint F C.Xl (Smlk i l k)) ∧
      (∀ i l, IsEndpoint F C.Xl (Sml0 i l)) ∧
      (∀ (i l : Fin q) (u : TestFunction F.V ℝ (⊤ : ℕ∞)),
        hasWeakWordDeriv C.Xl F.V [i.succ, l.succ] (fun x => a x * u x)
          (fun ξ => (Sml i l).apply (sumSquaresWithDrift C.Xl u) ξ +
            (∑ k : Fin q, (Smlk i l k).apply
              (fieldDerivative (C.Xl k.succ) (u : (Fin (n + m) → ℝ) → ℝ)) ξ) +
            (Sml0 i l).apply u ξ)) ∧
      (∀ (P : ℝ≥0∞) [Fact (1 ≤ P)] (hP1 : 1 < P) (hP : P ≠ ⊤) (u : (Fin (n + m) → ℝ) → ℝ)
          (D : List (Fin (q + 1)) → (Fin (n + m) → ℝ) → ℝ),
        memSobolevXZero w C.Xl F.V 2 P u → IsWeakJet w C.Xl F.V 2 P u D → ∀ i l : Fin q,
        hasWeakWordDeriv C.Xl F.V [i.succ, l.succ] (fun x => a x * u x)
          (fun ξ => (Sml i l).lpAct hF hP1 hP (weakSumSquaresWithDrift D) ξ +
            (∑ k : Fin q, (Smlk i l k).lpAct hF hP1 hP (D [k.succ]) ξ) +
            (Sml0 i l).lpAct hF hP1 hP u ξ)) := by
  obtain ⟨Sml, Smlk, Sml0, h1, h2, h3, hid⟩ := representation_secondOrder_of
    hF.lifted.contDiffOn_Xl hw0 hw B hRowInt hLeftDiff hRightDiff hTransfer hc hc0 a hParametrix
  exact ⟨Sml, Smlk, Sml0, h1, h2, h3, hid, fun P _ hP1 hP u D hu hD i l =>
    weakExtension_secondOrder hF hw0 hw hid hP1 hP hu hD i l⟩

end LiftedChart

end RothschildStein.P1
