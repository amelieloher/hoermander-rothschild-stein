-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.WeakExtensionHigher
public import RothschildStein.P1.RepresentationNoDriftSecondOrder

/-!
# No-drift parametrix and first- and second-order identities on `W^{2,p}_{X̃,0}(V)`

Without drift (alphabet `Fin k`, all weights one, `L̃ = sumSquares Xt = ∑ᵢ X̃ᵢ²`) the parametrix identity and the
first- and second-order representations extend to `u ∈ W^{2,p}_{X̃,0}(V)` (`memSobolevXZero`, `1 < p < ∞`) exactly as in the drift case
(`WeakExtensionParametrix`, `WeakExtensionBasic`), with `L̃u = ∑ᵢ D [i, i]` (`weakSumSquares D []`) and
`X̃ₖu = D [k]`, the weak jet `D` of `u`:

* `weakExtension_parametrix_left_noDrift`: `a u = P̄₂ (L̃u) + F̄₂ u` a.e. on `V` (from `a f = P₂ L̃f + F₂ f`);
* `weakExtension_firstOrder_noDrift`, `weakExtension_secondOrder_noDrift`: the first- and second-order
  representations with the bounded `L^p` extensions of the continuity theorem;
* `weakExtension_firstOrder_noDrift_of`, `weakExtension_secondOrder_noDrift_of`: under exactly the
  hypotheses of `representation_firstOrder_noDrift_of` resp. `representation_secondOrder_noDrift_of`
  (`LeftDifferentiation`, `TypeKernelIntegrable`, `RightDifferentiation`, `DerivativeTransfer`, `SignedParametrixNoDrift`, density data).

The first parametrix identity (`weakExtension_parametrix_adjoint`) is alphabet-generic. No regularity is asserted for
an arbitrary distribution.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal Topology BigOperators
namespace RothschildStein.P1

section Generic

variable {N k : ℕ} {F : KernelFrame N} {Xt : Fin k → (Fin N → ℝ) → (Fin N → ℝ)}
  {P : ℝ≥0∞} [Fact (1 ≤ P)] {w : Fin k → ℕ+}

/-- No drift: along tests approximating a jet of order two, `L̃ φ_j → L̃ u`
in `L^P(V)` (`L̃ = ∑ᵢ X̃ᵢ²`; the limit is the weak `L̃ u`, `weakSumSquares D []`). -/
theorem JetApprox.convLp_repSumSquaresTest
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (F.V : Set (Fin N → ℝ)))
    (hw : ∀ j, (w j : ℕ) = 1) {D : List (Fin k) → (Fin N → ℝ) → ℝ}
    {φ : ℕ → TestFunction F.V ℝ (⊤ : ℕ∞)} (h : JetApprox w Xt F.V 2 P D φ) :
    ConvLp F.V P (fun j => (repSumSquaresTest F Xt hXt (φ j) : (Fin N → ℝ) → ℝ))
      (weakSumSquares D []) := by
  have h1 := h.convLp_sumSquares hXt hw [] (by simp)
  have e : (fun j => (repSumSquaresTest F Xt hXt (φ j) : (Fin N → ℝ) → ℝ)) =
      fun j => (sumSquaresWordTest hXt [] (φ j) : (Fin N → ℝ) → ℝ) := by
    funext j
    rw [coe_repSumSquaresTest, coe_sumSquaresWordTest]
    rfl
  rw [e]
  exact h1

end Generic

namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}
  {r : ℕ} {H : H1.StandingHypotheses C.G r} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)} {P : ℝ≥0∞} [Fact (1 ≤ P)]

/-- **The second parametrix identity on `W^{2,P}_{X̃,0}(V)`, no drift**: if `a f = P₂ (L̃ f) + F₂ f`
on `V` for tests `f` (`L̃ = ∑ᵢ X̃ᵢ²`), then for `u ∈ W^{2,P}_{X̃,0}(V)` with weak jet `D`,
`a u = P̄₂ (L̃ u) + F̄₂ u` a.e. on `V`, `L̃ u = ∑ᵢ D [i, i]` the weak `L̃ u` and `P̄₂, F̄₂` the `L^P`
extensions of `P₂, F₂` (continuity theorem). -/
theorem weakExtension_parametrix_left_noDrift (hF : C.IsStandardFrame F H K hQ)
    (hw : ∀ j, (w j : ℕ) = 1) {a : TestFunction F.V ℝ (⊤ : ℕ∞)}
    {P₂ : TypeOperator F 2} {F₂ : TypeOperator F 1}
    (hzero : ∀ f : TestFunction F.V ℝ (⊤ : ℕ∞), ∀ ξ ∈ (F.V : Set (Fin (n + m) → ℝ)),
      a ξ * f ξ = P₂.apply (sumSquares C.Xl f) ξ + F₂.apply f ξ)
    (hP1 : 1 < P) (hP : P ≠ ⊤) {u : (Fin (n + m) → ℝ) → ℝ}
    (hu : memSobolevXZero w C.Xl F.V 2 P u) {D : List (Fin k) → (Fin (n + m) → ℝ) → ℝ}
    (hD : IsWeakJet w C.Xl F.V 2 P u D) :
    (fun x => a x * u x) =ᵐ[volume.restrict (F.V : Set (Fin (n + m) → ℝ))]
      fun ξ => P₂.lpAct hF hP1 hP (weakSumSquares D []) ξ + F₂.lpAct hF hP1 hP u ξ :=
  weakExtension_parametrix_left hF (repSumSquaresTest F C.Xl hF.lifted.contDiffOn_Xl)
    (fun u => coe_repSumSquaresTest hF.lifted.contDiffOn_Xl u) hzero hP1 hP hu hD
    (fun _ hφ => hφ.convLp_repSumSquaresTest hF.lifted.contDiffOn_Xl hw)

/-- **First-order representation, on `W^{2,P}_{X̃,0}(V)`, no drift**: if `X̃_l(a φ) = F_l L̃φ + S_l φ`
weakly on `V` for tests `φ` and generators `l`, then `X̃_l(a u) = F̄_l (L̃u) + S̄_l u` weakly on `V` for every
`u ∈ W^{2,P}_{X̃,0}(V)` with weak jet `D` (`L̃u = ∑ᵢ D [i, i]`), `1 < P < ∞`. -/
theorem weakExtension_firstOrder_noDrift (hF : C.IsStandardFrame F H K hQ)
    (hw : ∀ j, (w j : ℕ) = 1) {a : TestFunction F.V ℝ (⊤ : ℕ∞)} {Fl : Fin k → TypeOperator F 1}
    {Sl : Fin k → TypeOperator F 0}
    (hid : ∀ (l : Fin k) (u : TestFunction F.V ℝ (⊤ : ℕ∞)),
      hasWeakWordDeriv C.Xl F.V [l] (fun x => a x * u x)
        (fun ξ => (Fl l).apply (sumSquares C.Xl u) ξ + (Sl l).apply u ξ))
    (hP1 : 1 < P) (hP : P ≠ ⊤) {u : (Fin (n + m) → ℝ) → ℝ}
    (hu : memSobolevXZero w C.Xl F.V 2 P u) {D : List (Fin k) → (Fin (n + m) → ℝ) → ℝ}
    (hD : IsWeakJet w C.Xl F.V 2 P u D) (l : Fin k) :
    hasWeakWordDeriv C.Xl F.V [l] (fun x => a x * u x)
      (fun ξ => (Fl l).lpAct hF hP1 hP (weakSumSquares D []) ξ + (Sl l).lpAct hF hP1 hP u ξ) := by
  have hXt := hF.lifted.contDiffOn_Xl
  refine weakExtension_mul hXt hF.lifted.volume_lt_top hu hD a [l]
    (fun f ξ => (Fl l).apply (sumSquares C.Xl f) ξ + (Sl l).apply f ξ) _
    (fun φ hφ => ?_) (hid l)
  have h1 := (Fl l).convLp_apply hF hP1 hP (hφ.convLp_repSumSquaresTest hXt hw)
  simp only [coe_repSumSquaresTest] at h1
  exact h1.add ((Sl l).convLp_apply hF hP1 hP (hφ.convLp_nil hD))

/-- **Second-order representation, on `W^{2,P}_{X̃,0}(V)`, no drift**: if
`X̃_i X̃_l(a φ) = S_il L̃φ + ∑ₖ S_ilk X̃ₖφ + S_il0 φ` weakly on `V` for tests `φ`, then the same identity holds
with the bounded extensions `S̄` for every `u ∈ W^{2,P}_{X̃,0}(V)` with weak jet `D` (`X̃ₖu = D [k]`). -/
theorem weakExtension_secondOrder_noDrift (hF : C.IsStandardFrame F H K hQ)
    (hw : ∀ j, (w j : ℕ) = 1) {a : TestFunction F.V ℝ (⊤ : ℕ∞)}
    {Sml : Fin k → Fin k → TypeOperator F 0} {Smlk : Fin k → Fin k → Fin k → TypeOperator F 0}
    {Sml0 : Fin k → Fin k → TypeOperator F 0}
    (hid : ∀ (i l : Fin k) (u : TestFunction F.V ℝ (⊤ : ℕ∞)),
      hasWeakWordDeriv C.Xl F.V [i, l] (fun x => a x * u x)
        (fun ξ => (Sml i l).apply (sumSquares C.Xl u) ξ +
          (∑ j : Fin k, (Smlk i l j).apply
            (fieldDerivative (C.Xl j) (u : (Fin (n + m) → ℝ) → ℝ)) ξ) +
          (Sml0 i l).apply u ξ))
    (hP1 : 1 < P) (hP : P ≠ ⊤) {u : (Fin (n + m) → ℝ) → ℝ}
    (hu : memSobolevXZero w C.Xl F.V 2 P u) {D : List (Fin k) → (Fin (n + m) → ℝ) → ℝ}
    (hD : IsWeakJet w C.Xl F.V 2 P u D) (i l : Fin k) :
    hasWeakWordDeriv C.Xl F.V [i, l] (fun x => a x * u x)
      (fun ξ => (Sml i l).lpAct hF hP1 hP (weakSumSquares D []) ξ +
        (∑ j : Fin k, (Smlk i l j).lpAct hF hP1 hP (D [j]) ξ) +
        (Sml0 i l).lpAct hF hP1 hP u ξ) := by
  have hXt := hF.lifted.contDiffOn_Xl
  refine weakExtension_mul hXt hF.lifted.volume_lt_top hu hD a [i, l]
    (fun f ξ => (Sml i l).apply (sumSquares C.Xl f) ξ +
      (∑ j : Fin k, (Smlk i l j).apply
        (fieldDerivative (C.Xl j) (f : (Fin (n + m) → ℝ) → ℝ)) ξ) +
      (Sml0 i l).apply f ξ) _ (fun φ hφ => ?_) (hid i l)
  have h1 := (Sml i l).convLp_apply hF hP1 hP (hφ.convLp_repSumSquaresTest hXt hw)
  simp only [coe_repSumSquaresTest] at h1
  have h2 : ConvLp F.V P (fun j ξ => ∑ t : Fin k, (Smlk i l t).apply
      (fieldDerivative (C.Xl t) (φ j : (Fin (n + m) → ℝ) → ℝ)) ξ)
      (fun ξ => ∑ t : Fin k, (Smlk i l t).lpAct hF hP1 hP (D [t]) ξ) :=
    ConvLp.finset_sum Finset.univ fun t _ => (Smlk i l t).convLp_apply hF hP1 hP
      (ψ := fun j => S.wordDerivativeTest F.V C.Xl hXt [t] (φ j))
      (hφ [t] ((S.mem_wordFamily_iff w 2 _).2 (by simp [wordWeight, hw t])))
  exact (h1.add h2).add ((Sml0 i l).convLp_apply hF hP1 hP (hφ.convLp_nil hD))

/-- **First-order representation, no drift: representation and extension.** Under the hypotheses of
`representation_firstOrder_noDrift_of` (`LeftDifferentiation`, `SignedParametrixNoDrift`, the density data), there are type-1
`F_l` and endpoint type-0 `S_l` with `X̃_l(a u) = F_l L̃u + S_l u` for tests `u`, and for every `1 < P < ∞` and
`u ∈ W^{2,P}_{X̃,0}(V)` with weak jet `D`, `X̃_l(a u) = F̄_l L̃u + S̄_l u` in distributions with the `L^P`
representatives of the continuity theorem (`L̃u = ∑ᵢ D [i, i]`). -/
theorem weakExtension_firstOrder_noDrift_of (hF : C.IsStandardFrame F H K hQ)
    (hw : ∀ j, (w j : ℕ) = 1) (hLeftDiff : LeftDifferentiation F w C.Xl)
    {c : (Fin (n + m) → ℝ) → ℝ} (hc : ContDiffOn ℝ (⊤ : ℕ∞) c (F.V : Set (Fin (n + m) → ℝ)))
    (hc0 : ∀ ξ ∈ (F.V : Set (Fin (n + m) → ℝ)), 0 < c ξ) (a : TestFunction F.V ℝ (⊤ : ℕ∞))
    (hParametrix : ∀ b : TestFunction F.V ℝ (⊤ : ℕ∞), SignedParametrixNoDrift F C.Xl c a b) :
    ∃ (Fl : Fin k → TypeOperator F 1) (Sl : Fin k → TypeOperator F 0),
      (∀ l, IsEndpoint F C.Xl (Sl l)) ∧
      (∀ (l : Fin k) (u : TestFunction F.V ℝ (⊤ : ℕ∞)),
        hasWeakWordDeriv C.Xl F.V [l] (fun x => a x * u x)
          (fun ξ => (Fl l).apply (sumSquares C.Xl u) ξ + (Sl l).apply u ξ)) ∧
      (∀ (P : ℝ≥0∞) [Fact (1 ≤ P)] (hP1 : 1 < P) (hP : P ≠ ⊤) (u : (Fin (n + m) → ℝ) → ℝ)
          (D : List (Fin k) → (Fin (n + m) → ℝ) → ℝ),
        memSobolevXZero w C.Xl F.V 2 P u → IsWeakJet w C.Xl F.V 2 P u D → ∀ l : Fin k,
        hasWeakWordDeriv C.Xl F.V [l] (fun x => a x * u x)
          (fun ξ => (Fl l).lpAct hF hP1 hP (weakSumSquares D []) ξ +
            (Sl l).lpAct hF hP1 hP u ξ)) := by
  obtain ⟨Fl, Sl, hend, hid⟩ :=
    representation_firstOrder_noDrift_of hF.lifted.contDiffOn_Xl hw hLeftDiff hc hc0 a hParametrix
  exact ⟨Fl, Sl, hend, hid, fun P _ hP1 hP u D hu hD l =>
    weakExtension_firstOrder_noDrift hF hw hid hP1 hP hu hD l⟩

/-- **Second-order representation, no drift: representation and extension.** Under the hypotheses of
`representation_secondOrder_noDrift_of` (`TypeKernelIntegrable`, `LeftDifferentiation`, `RightDifferentiation`, `DerivativeTransfer`,
`SignedParametrixNoDrift`), the type-0 endpoint operators `S_il, S_ilk, S_il0` satisfy
`X̃_i X̃_l(a u) = S_il L̃u + ∑ₖ S_ilk X̃ₖu + S_il0 u` for tests `u`, and the same identity with the bounded
extensions for every `u ∈ W^{2,P}_{X̃,0}(V)`, `1 < P < ∞`. -/
theorem weakExtension_secondOrder_noDrift_of (hF : C.IsStandardFrame F H K hQ)
    (hw : ∀ j, (w j : ℕ) = 1) (B : Fin (n + m) → List (Fin k)) (hRowInt : TypeKernelIntegrable F)
    (hLeftDiff : LeftDifferentiation F w C.Xl) (hRightDiff : RightDifferentiation F w C.Xl hF.lifted.contDiffOn_Xl)
    (hTransfer : DerivativeTransfer F w C.Xl B)
    {c : (Fin (n + m) → ℝ) → ℝ} (hc : ContDiffOn ℝ (⊤ : ℕ∞) c (F.V : Set (Fin (n + m) → ℝ)))
    (hc0 : ∀ ξ ∈ (F.V : Set (Fin (n + m) → ℝ)), 0 < c ξ) (a : TestFunction F.V ℝ (⊤ : ℕ∞))
    (hParametrix : ∀ b : TestFunction F.V ℝ (⊤ : ℕ∞), SignedParametrixNoDrift F C.Xl c a b) :
    ∃ (Sml : Fin k → Fin k → TypeOperator F 0)
      (Smlk : Fin k → Fin k → Fin k → TypeOperator F 0)
      (Sml0 : Fin k → Fin k → TypeOperator F 0),
      (∀ i l, IsEndpoint F C.Xl (Sml i l)) ∧ (∀ i l j, IsEndpoint F C.Xl (Smlk i l j)) ∧
      (∀ i l, IsEndpoint F C.Xl (Sml0 i l)) ∧
      (∀ (i l : Fin k) (u : TestFunction F.V ℝ (⊤ : ℕ∞)),
        hasWeakWordDeriv C.Xl F.V [i, l] (fun x => a x * u x)
          (fun ξ => (Sml i l).apply (sumSquares C.Xl u) ξ +
            (∑ j : Fin k, (Smlk i l j).apply
              (fieldDerivative (C.Xl j) (u : (Fin (n + m) → ℝ) → ℝ)) ξ) +
            (Sml0 i l).apply u ξ)) ∧
      (∀ (P : ℝ≥0∞) [Fact (1 ≤ P)] (hP1 : 1 < P) (hP : P ≠ ⊤) (u : (Fin (n + m) → ℝ) → ℝ)
          (D : List (Fin k) → (Fin (n + m) → ℝ) → ℝ),
        memSobolevXZero w C.Xl F.V 2 P u → IsWeakJet w C.Xl F.V 2 P u D → ∀ i l : Fin k,
        hasWeakWordDeriv C.Xl F.V [i, l] (fun x => a x * u x)
          (fun ξ => (Sml i l).lpAct hF hP1 hP (weakSumSquares D []) ξ +
            (∑ j : Fin k, (Smlk i l j).lpAct hF hP1 hP (D [j]) ξ) +
            (Sml0 i l).lpAct hF hP1 hP u ξ)) := by
  obtain ⟨Sml, Smlk, Sml0, h1, h2, h3, hid⟩ := representation_secondOrder_noDrift_of
    hF.lifted.contDiffOn_Xl hw B hRowInt hLeftDiff hRightDiff hTransfer hc hc0 a hParametrix
  exact ⟨Sml, Smlk, Sml0, h1, h2, h3, hid, fun P _ hP1 hP u D hu hD i l =>
    weakExtension_secondOrder_noDrift hF hw hid hP1 hP hu hD i l⟩

end LiftedChart

end RothschildStein.P1
