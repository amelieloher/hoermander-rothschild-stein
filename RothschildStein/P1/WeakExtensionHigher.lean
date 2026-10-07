-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.WeakExtensionJet
public import RothschildStein.P1.WeakExtensionParametrix
public import RothschildStein.P1.RepresentationHigher

/-!
# Higher-order identities on `W^{m,p}_{X̃,0}(V)` without drift

The higher-order no-drift representation (BB pp. 565–566, Thm 11.28),
`X̃_I(a u) = ∑_J S_IJ X̃_J L̃u + ∑_K T_IK X̃_K u` for tests `u` (endpoint type-0 families
`S_IJ`, `|J| ≤ m - 2`, `T_IK`, `|K| ≤ m - 1`, `m = |I| ≥ 2`, all weights one, `L̃ = ∑ᵢ X̃ᵢ²`), extends to
every `u ∈ W^{m,p}_{X̃,0}(V)` (closure of the tests in the `W^{m,p}_{X̃}` norm, `1 < p < ∞`):

`X̃_I(a u) = ∑_J S̄_IJ (X̃_J L̃u) + ∑_K T̄_IK (X̃_K u)` in distributions on `V`,

where `X̃_K u = D K` and `X̃_J L̃u = ∑ᵢ D (J ++ [i, i])` (`weakSumSquares`) are the weak derivatives of the
jet `D` of `u` (consistent with each other: `IsWeakJet.hasWeakWordDeriv_sumSquares`) and `S̄, T̄` are the
bounded `L^p` extensions of the continuity theorem (the indicated `L^p` representatives). There is no higher formula
with drift, and no regularity is asserted for an arbitrary distribution.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal Topology
namespace RothschildStein.P1

namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}
  {r : ℕ} {H : H1.StandingHypotheses C.G r} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)} {P : ℝ≥0∞} [Fact (1 ≤ P)]

/-- **The higher-order representation on `W^{|I|,P}_{X̃,0}(V)`** (no drift, all weights one): if, for a word `I` of
length `≥ 2`, `X̃_I(a φ) = ∑_J S_J (X̃_J L̃φ) + ∑_K T_K (X̃_K φ)` weakly on `V` for every test `φ`
(`J ∈ repWords k (|I| - 2)`, `K ∈ repWords k (|I| - 1)`, `S_J, T_K` of type 0), then for every
`u ∈ W^{|I|,P}_{X̃,0}(V)` with weak jet `D`, `1 < P < ∞`,
`X̃_I(a u) = ∑_J S̄_J (∑ᵢ D (J ++ [i, i])) + ∑_K T̄_K (D K)` weakly on `V`. -/
theorem weakExtension_higher (hF : C.IsStandardFrame F H K hQ) (hw : ∀ j, (w j : ℕ) = 1)
    {a : TestFunction F.V ℝ (⊤ : ℕ∞)} (I : List (Fin k)) (hI : 2 ≤ I.length)
    {Sf Tf : List (Fin k) → TypeOperator F 0}
    (hid : ∀ u : TestFunction F.V ℝ (⊤ : ℕ∞),
      hasWeakWordDeriv C.Xl F.V I (fun x => a x * u x)
        (fun ξ => (∑ J ∈ repWords k (I.length - 2),
            (Sf J).apply (wordDerivative C.Xl J (sumSquares C.Xl (u : (Fin (n + m) → ℝ) → ℝ))) ξ) +
          ∑ K ∈ repWords k (I.length - 1),
            (Tf K).apply (wordDerivative C.Xl K (u : (Fin (n + m) → ℝ) → ℝ)) ξ))
    (hP1 : 1 < P) (hP : P ≠ ⊤) {u : (Fin (n + m) → ℝ) → ℝ}
    (hu : memSobolevXZero w C.Xl F.V I.length P u) {D : List (Fin k) → (Fin (n + m) → ℝ) → ℝ}
    (hD : IsWeakJet w C.Xl F.V I.length P u D) :
    hasWeakWordDeriv C.Xl F.V I (fun x => a x * u x)
      (fun ξ => (∑ J ∈ repWords k (I.length - 2),
          (Sf J).lpAct hF hP1 hP (weakSumSquares D J) ξ) +
        ∑ K ∈ repWords k (I.length - 1), (Tf K).lpAct hF hP1 hP (D K) ξ) := by
  have hXt := hF.lifted.contDiffOn_Xl
  refine weakExtension_mul hXt hF.lifted.volume_lt_top hu hD a I
    (fun f ξ => (∑ J ∈ repWords k (I.length - 2),
        (Sf J).apply (wordDerivative C.Xl J (sumSquares C.Xl (f : (Fin (n + m) → ℝ) → ℝ))) ξ) +
      ∑ K ∈ repWords k (I.length - 1),
        (Tf K).apply (wordDerivative C.Xl K (f : (Fin (n + m) → ℝ) → ℝ)) ξ) _
    (fun φ hφ => ?_) hid
  have h1 : ConvLp F.V P (fun j ξ => ∑ J ∈ repWords k (I.length - 2),
      (Sf J).apply (wordDerivative C.Xl J (sumSquares C.Xl (φ j : (Fin (n + m) → ℝ) → ℝ))) ξ)
      (fun ξ => ∑ J ∈ repWords k (I.length - 2), (Sf J).lpAct hF hP1 hP (weakSumSquares D J) ξ) :=
    ConvLp.finset_sum _ fun J hJ => by
      have hJ' := mem_repWords.1 hJ
      have := (Sf J).convLp_apply hF hP1 hP (ψ := fun j => sumSquaresWordTest hXt J (φ j))
        (hφ.convLp_sumSquares hXt hw J (by omega))
      simpa only [coe_sumSquaresWordTest] using this
  have h2 : ConvLp F.V P (fun j ξ => ∑ K ∈ repWords k (I.length - 1),
      (Tf K).apply (wordDerivative C.Xl K (φ j : (Fin (n + m) → ℝ) → ℝ)) ξ)
      (fun ξ => ∑ K ∈ repWords k (I.length - 1), (Tf K).lpAct hF hP1 hP (D K) ξ) :=
    ConvLp.finset_sum _ fun K hK => (Tf K).convLp_apply hF hP1 hP
      (ψ := fun j => S.wordDerivativeTest F.V C.Xl hXt K (φ j))
      (hφ K ((S.mem_wordFamily_iff w _ K).2 (by
        have := mem_repWords.1 hK
        rw [wordWeight_eq_length hw]
        omega)))
  exact h1.add h2

/-- **Higher-order representation: representation and extension.** Under the hypotheses of
`representation_higher_noDrift_of` (the exact statements `TypeKernelIntegrable`, `LeftDifferentiation`, `RightDifferentiation`,
`DerivativeTransfer` and `SignedParametrixNoDrift`, all weights one), for every word `I` of length `m ≥ 2`
there are endpoint type-0 families `S_IJ`, `T_IK` with `X̃_I(a u) = ∑_J S_IJ X̃_J L̃u + ∑_K T_IK X̃_K u`
for tests `u`, and the same identity with the bounded extensions `S̄, T̄` and the weak jet of `u`, for
every `u ∈ W^{m,P}_{X̃,0}(V)`, `1 < P < ∞`. -/
theorem weakExtension_higher_of (hF : C.IsStandardFrame F H K hQ) (hw : ∀ j, (w j : ℕ) = 1)
    (B : Fin (n + m) → List (Fin k)) (hRowInt : TypeKernelIntegrable F) (hLeftDiff : LeftDifferentiation F w C.Xl)
    (hRightDiff : RightDifferentiation F w C.Xl hF.lifted.contDiffOn_Xl) (hTransfer : DerivativeTransfer F w C.Xl B)
    {c : (Fin (n + m) → ℝ) → ℝ} (hc : ContDiffOn ℝ (⊤ : ℕ∞) c (F.V : Set (Fin (n + m) → ℝ)))
    (hc0 : ∀ ξ ∈ (F.V : Set (Fin (n + m) → ℝ)), 0 < c ξ) (a : TestFunction F.V ℝ (⊤ : ℕ∞))
    (hParametrix : ∀ b : TestFunction F.V ℝ (⊤ : ℕ∞), SignedParametrixNoDrift F C.Xl c a b)
    (I : List (Fin k)) (hI : 2 ≤ I.length) :
    ∃ Sf Tf : List (Fin k) → TypeOperator F 0,
      (∀ J, IsEndpoint F C.Xl (Sf J)) ∧ (∀ K, IsEndpoint F C.Xl (Tf K)) ∧
      (∀ u : TestFunction F.V ℝ (⊤ : ℕ∞),
        hasWeakWordDeriv C.Xl F.V I (fun x => a x * u x)
          (fun ξ => (∑ J ∈ repWords k (I.length - 2),
              (Sf J).apply (wordDerivative C.Xl J (sumSquares C.Xl (u : (Fin (n + m) → ℝ) → ℝ))) ξ) +
            ∑ K ∈ repWords k (I.length - 1),
              (Tf K).apply (wordDerivative C.Xl K (u : (Fin (n + m) → ℝ) → ℝ)) ξ)) ∧
      (∀ (P : ℝ≥0∞) [Fact (1 ≤ P)] (hP1 : 1 < P) (hP : P ≠ ⊤) (u : (Fin (n + m) → ℝ) → ℝ)
          (D : List (Fin k) → (Fin (n + m) → ℝ) → ℝ),
        memSobolevXZero w C.Xl F.V I.length P u → IsWeakJet w C.Xl F.V I.length P u D →
        hasWeakWordDeriv C.Xl F.V I (fun x => a x * u x)
          (fun ξ => (∑ J ∈ repWords k (I.length - 2),
              (Sf J).lpAct hF hP1 hP (weakSumSquares D J) ξ) +
            ∑ K ∈ repWords k (I.length - 1), (Tf K).lpAct hF hP1 hP (D K) ξ)) := by
  obtain ⟨Sf, Tf, hS, hT, hid⟩ := representation_higher_noDrift_of hF.lifted.contDiffOn_Xl hw B hRowInt
    hLeftDiff hRightDiff hTransfer hc hc0 a hParametrix I hI
  exact ⟨Sf, Tf, hS, hT, hid, fun P _ hP1 hP u D hu hD =>
    weakExtension_higher hF hw I hI hid hP1 hP hu hD⟩

end LiftedChart

end RothschildStein.P1
