-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.LiftedDistanceGeometryWeakExtension
public import RothschildStein.P1.HigherNormSobolev
public import RothschildStein.P1.HigherNormHolderJets
public import RothschildStein.P1.GainHolder
public import RothschildStein.P1.RepresentationForms

/-!
# One more derivative of the type-0 endpoint operators

Part of the higher Hölder estimate (BB p. 604, proof of Thm 11.59: rewrite `S = X̃_j F`, commute `X̃_j` to its
inputs, and then differentiate). For a type-0 endpoint operator `S = ∑ₜ X̃_{jₜ} Gₜ` (`IsEndpoint`, `Gₜ`
of type 1), no drift, and a generator `X̃_i`:

* on tests `g`, the no-drift commutation (`RepComm`, the commutation formula) turns `S g = ∑ₜ X̃_{jₜ}(Gₜ g)` into
  `∑ₜ (∑_l G_{t l} X̃_l g + G_{t 0} g)` with type-1 `G_{t l}, G_{t 0}`, and left differentiation
  (`LeftDifferentiation`) differentiates every term once more:
  `X̃_i (S g) = ∑ₜ (∑_l Q_{t l} (X̃_l g) + Q_{t 0} g)` with type-0 `Q_{t l}, Q_{t 0}`
  (`exists_endpointDiff_tests`);
* the identity extends to every `h ∈ W^{1,2}_{X̃,0}(V)` with weak jet `D h`, with the bounded `L^2`
  extensions of the continuity theorem (`endpointDiff_lp`). The inputs are of order one only, so no regularity beyond the
  first derivative of the input is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal Topology BigOperators
namespace RothschildStein.P2.HigherHolder

open RothschildStein.P1

section Tests

variable {N k : ℕ} {F : KernelFrame N} {w : Fin k → ℕ+}
  {Xt : Fin k → (Fin N → ℝ) → (Fin N → ℝ)}

/-- **One more derivative of an endpoint operator on tests** (no drift).
For an endpoint operator `S` of type `0` and a generator `i` there are finitely many type-`0` operators
`Q t l`, `Q0 t` with `X̃_i (S g) = ∑ₜ (∑_l Q_{t l} (X̃_l g) + Q_{t 0} g)` weakly on `V`, for every test `g`. -/
theorem exists_endpointDiff_tests
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (F.V : Set (Fin N → ℝ)))
    (hw : ∀ j, (w j : ℕ) = 1) (hLeftDiff : LeftDifferentiation F w Xt) (hcomm : RepComm F Xt)
    {Sop : TypeOperator F 0} (hS : IsEndpoint F Xt Sop) (i : Fin k) :
    ∃ (r : ℕ) (Q : Fin r → Fin k → TypeOperator F 0) (Q0 : Fin r → TypeOperator F 0),
      ∀ g : TestFunction F.V ℝ (⊤ : ℕ∞),
        hasWeakWordDeriv Xt F.V [i] (Sop.apply (g : (Fin N → ℝ) → ℝ))
          (fun ξ => ∑ t, ((∑ l, (Q t l).apply (fieldDerivative (Xt l) (g : (Fin N → ℝ) → ℝ)) ξ) +
            (Q0 t).apply (g : (Fin N → ℝ) → ℝ) ξ)) := by
  classical
  obtain ⟨r, j, G, hG⟩ := hS
  choose Fh F0 hFt using fun t : Fin r => hcomm (G t) (j t)
  choose Q hQ using fun (t : Fin r) (l : Fin k) =>
    exists_leftOp_of_eq (lam' := 0) hLeftDiff (Fh t l) i (by have := hw i; omega)
      (by have := hw i; omega)
  choose Q0 hQ0 using fun t : Fin r =>
    exists_leftOp_of_eq (lam' := 0) hLeftDiff (F0 t) i (by have := hw i; omega)
      (by have := hw i; omega)
  refine ⟨r, Q, Q0, fun g => ?_⟩
  obtain ⟨h, hh, hSg⟩ := hG g
  have hrhs : ∀ t : Fin r, hasWeakWordDeriv Xt F.V [i]
      (fun ξ => (∑ l, (Fh t l).apply (fieldDerivative (Xt l) (g : (Fin N → ℝ) → ℝ)) ξ) +
        (F0 t).apply (g : (Fin N → ℝ) → ℝ) ξ)
      (fun ξ => (∑ l, (Q t l).apply (fieldDerivative (Xt l) (g : (Fin N → ℝ) → ℝ)) ξ) +
        (Q0 t).apply (g : (Fin N → ℝ) → ℝ) ξ) := by
    intro t
    have h1 := repWeak_finset_sum hXt [i] Finset.univ
      (fun l ξ => (Fh t l).apply (fieldDerivative (Xt l) (g : (Fin N → ℝ) → ℝ)) ξ)
      (fun l ξ => (Q t l).apply (fieldDerivative (Xt l) (g : (Fin N → ℝ) → ℝ)) ξ)
      (fun l _ => hQ t l (S.wordDerivativeTest F.V Xt hXt [l] g))
    exact S.hasWeakWordDeriv_add Xt F.V hXt h1 (hQ0 t g)
  have hht : ∀ t : Fin r, h t =ᵐ[volume.restrict (F.V : Set (Fin N → ℝ))]
      (fun ξ => (∑ l, (Fh t l).apply (fieldDerivative (Xt l) (g : (Fin N → ℝ) → ℝ)) ξ) +
        (F0 t).apply (g : (Fin N → ℝ) → ℝ) ξ) := fun t =>
    S.hasWeakWordDeriv_unique Xt F.V (hh t) (hFt t g)
  have hsum := repWeak_finset_sum hXt [i] Finset.univ
    (fun t ξ => (∑ l, (Fh t l).apply (fieldDerivative (Xt l) (g : (Fin N → ℝ) → ℝ)) ξ) +
      (F0 t).apply (g : (Fin N → ℝ) → ℝ) ξ)
    (fun t ξ => (∑ l, (Q t l).apply (fieldDerivative (Xt l) (g : (Fin N → ℝ) → ℝ)) ξ) +
      (Q0 t).apply (g : (Fin N → ℝ) → ℝ) ξ) (fun t _ => hrhs t)
  refine S.hasWeakWordDeriv_congr_ae Xt F.V hsum ?_ Filter.EventuallyEq.rfl
  rw [hSg]
  exact (ae_eq_finset_sum Finset.univ fun t _ => hht t).symm

end Tests

section Extension

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}
  {r : ℕ} {H : H1.StandingHypotheses C.G r} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)}

/-- **`exists_endpointDiff_tests` on `W^{1,2}_{X̃,0}(V)`**: with the same
operators `Q t l`, `Q0 t`, for every `h ∈ W^{1,2}_{X̃,0}(V)` with weak jet `D h`,
`X̃_i (S̄ h) = ∑ₜ (∑_l Q̄_{t l} (D h [l]) + Q̄_{t 0} h)` weakly on `V` (bounded `L^2` extensions, by the continuity theorem). -/
theorem endpointDiff_lp (hF : C.IsStandardFrame F H K hQ) (hw : ∀ j, (w j : ℕ) = 1)
    (hLeftDiff : LeftDifferentiation F w C.Xl) (hcomm : RepComm F C.Xl) {Sop : TypeOperator F 0}
    (hS : IsEndpoint F C.Xl Sop) (i : Fin k) :
    ∃ (r' : ℕ) (Q : Fin r' → Fin k → TypeOperator F 0) (Q0 : Fin r' → TypeOperator F 0),
      ∀ (h : (Fin (n + m) → ℝ) → ℝ) (Dh : List (Fin k) → (Fin (n + m) → ℝ) → ℝ),
        memSobolevXZero w C.Xl F.V 1 2 h → IsWeakJet w C.Xl F.V 1 2 h Dh →
        hasWeakWordDeriv C.Xl F.V [i]
          (Sop.lpAct hF (P := 2) (by norm_num) (by simp) h)
          (fun ξ => ∑ t, ((∑ l, (Q t l).lpAct hF (P := 2) (by norm_num) (by simp) (Dh [l]) ξ) +
            (Q0 t).lpAct hF (P := 2) (by norm_num) (by simp) h ξ)) := by
  classical
  have hXt := hF.lifted.contDiffOn_Xl
  have : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨one_le_two⟩
  have hP1 : (1 : ℝ≥0∞) < 2 := by norm_num
  have hP : (2 : ℝ≥0∞) ≠ ⊤ := by simp
  obtain ⟨r', Q, Q0, hid⟩ := exists_endpointDiff_tests hXt hw hLeftDiff hcomm hS i
  refine ⟨r', Q, Q0, fun h Dh hh hD => ?_⟩
  have hmem : ∀ l : Fin k, [l] ∈ wordFamily w 1 := fun l => by
    rw [S.mem_wordFamily_iff, wordWeight_eq_length hw]; simp
  refine weakExtension_limit hXt hF.lifted.volume_lt_top hh hD [i]
    (fun φ => Sop.apply (φ : (Fin (n + m) → ℝ) → ℝ))
    (fun φ ξ => ∑ t, ((∑ l, (Q t l).apply (fieldDerivative (C.Xl l) (φ : (Fin (n + m) → ℝ) → ℝ)) ξ) +
      (Q0 t).apply (φ : (Fin (n + m) → ℝ) → ℝ) ξ))
    (Sop.lpAct hF hP1 hP h)
    (fun ξ => ∑ t, ((∑ l, (Q t l).lpAct hF hP1 hP (Dh [l]) ξ) + (Q0 t).lpAct hF hP1 hP h ξ))
    (fun φ hφ => ?_) (fun φ hφ => ?_) hid
  · have h0 : ConvLp F.V 2 (fun j => (φ j : (Fin (n + m) → ℝ) → ℝ)) h :=
      (hφ [] (S.nil_mem_wordFamily w 1)).congr_ae (fun _ => Filter.EventuallyEq.rfl) hD.nil_ae
    exact Sop.convLp_apply hF hP1 hP h0
  · have h0 : ConvLp F.V 2 (fun j => (φ j : (Fin (n + m) → ℝ) → ℝ)) h :=
      (hφ [] (S.nil_mem_wordFamily w 1)).congr_ae (fun _ => Filter.EventuallyEq.rfl) hD.nil_ae
    refine ConvLp.finset_sum Finset.univ fun t _ => ?_
    refine ConvLp.add (ConvLp.finset_sum Finset.univ fun l _ => ?_) ((Q0 t).convLp_apply hF hP1 hP h0)
    exact (Q t l).convLp_apply hF hP1 hP
      (ψ := fun j => S.wordDerivativeTest F.V C.Xl hXt [l] (φ j)) (hφ [l] (hmem l))

end Extension

end RothschildStein.P2.HigherHolder
