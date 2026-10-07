-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.WeakExtensionSupport
public import RothschildStein.P1.RepresentationBasic

/-!
# Weak extension: approximating sequences of jets and the action of `T̄` on them

Tools shared by all the extensions of the parametrix and representation identities to `W^{m,p}_{X̃,0}(V)`:

* `exists_testSeq_convLp`: every `g ∈ L^P(V)`, `P < ∞`, is the `L^P` limit of tests;
* `JetApprox`: a sequence of tests approximates the weak jet `D` (`X̃_K φ_j → D K` in `L^P(V)` for
  every word `K` of weight at most `kk`), and `weakSumSquares`, the weak `X̃_J L̃ u = ∑ᵢ D (J ++ [i, i])`;
* `TypeOperator.convLp_apply`: `L^P` convergence of tests `ψ_j → g` gives `T ψ_j → T̄ g` in `L^P(V)`
  (boundedness, by the continuity theorem), `MultEndpoint.convLp_apply` for the coefficients of the drift representation;
* `weakExtension_mul`: the limit statement for the left side `a u`, `a ∈ C_c^∞(V)` (the
  left-hand derivatives converge in distributions).

None of this gives regularity of an arbitrary distribution: all inputs are in the closure of the tests
(`memSobolevXZero`) or in `L^P(V)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal Topology
namespace RothschildStein.P1

section Sequences

variable {N k : ℕ} {Xt : Fin k → (Fin N → ℝ) → (Fin N → ℝ)} {V : Opens (Fin N → ℝ)}
  {P : ℝ≥0∞} [Fact (1 ≤ P)]

/-- **Tests are `L^P`-dense**: every `g ∈ L^P(V)`, `1 ≤ P < ∞`, is the
`L^P(V)` limit of a sequence of tests. -/
theorem exists_testSeq_convLp (hfin : volume (V : Set (Fin N → ℝ)) < ⊤) (hP : P ≠ ⊤)
    {g : (Fin N → ℝ) → ℝ} (hg : MemLp g P (volume.restrict (V : Set (Fin N → ℝ)))) :
    ∃ φ : ℕ → TestFunction V ℝ (⊤ : ℕ∞), ConvLp V P (fun j => (φ j : (Fin N → ℝ) → ℝ)) g := by
  have hmem : hg.toLp g ∈ closure (Set.range (testToLp V hfin P)) := by
    rw [(denseRange_testToLp V hfin hP).closure_eq]
    exact Set.mem_univ _
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 hmem
  choose φ hφ using hu
  refine ⟨φ, fun j => testFunction_memLp V hfin (φ j) P, hg, ?_⟩
  have e : (fun j => (testFunction_memLp V hfin (φ j) P).toLp (φ j)) = u :=
    funext fun j => hφ j
  rw [e]
  exact hlim

/-- A test function is bounded. -/
theorem exists_abs_le_test (a : TestFunction V ℝ (⊤ : ℕ∞)) : ∃ M : ℝ, ∀ x, |a x| ≤ M := by
  obtain ⟨M, hM⟩ := a.continuous.bounded_above_of_compact_support a.hasCompactSupport
  exact ⟨M, fun x => by simpa using hM x⟩

variable {f f' : ℕ → (Fin N → ℝ) → ℝ} {g g' : (Fin N → ℝ) → ℝ}

/-- Multiplication by a test function preserves `L^P` convergence. -/
theorem ConvLp.mul_test (a : TestFunction V ℝ (⊤ : ℕ∞)) (h : ConvLp V P f g) :
    ConvLp V P (fun j x => a x * f j x) (fun x => a x * g x) := by
  obtain ⟨M, hM⟩ := exists_abs_le_test a
  exact ConvLp.mul_bounded a.continuous.aestronglyMeasurable hM h

end Sequences

section JetApprox

variable {N k : ℕ} {Xt : Fin k → (Fin N → ℝ) → (Fin N → ℝ)} {V : Opens (Fin N → ℝ)}
  {P : ℝ≥0∞} [Fact (1 ≤ P)]

/-- The tests `φ_j` **approximate the weak jet** `D` of weight at most
`kk`: `X̃_K φ_j → D K` in `L^P(V)` for every word `K` with `|K|_w ≤ kk`
(BB Thm 2.9, `exists_testSeq_convLp_jet`). -/
def JetApprox (w : Fin k → ℕ+) (Xt : Fin k → (Fin N → ℝ) → (Fin N → ℝ)) (V : Opens (Fin N → ℝ))
    (kk : ℕ) (P : ℝ≥0∞) [Fact (1 ≤ P)] (D : List (Fin k) → (Fin N → ℝ) → ℝ)
    (φ : ℕ → TestFunction V ℝ (⊤ : ℕ∞)) : Prop :=
  ∀ K ∈ wordFamily w kk,
    ConvLp V P (fun j => wordDerivative Xt K (φ j : (Fin N → ℝ) → ℝ)) (D K)

/-- For `u ∈ W^{kk,P}_{X̃,0}(V)` with weak jet `D` there are tests
`φ_j → u` in `L^P(V)` with `φ_j` approximating the jet. -/
theorem exists_jetApprox {w : Fin k → ℕ+}
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (V : Set (Fin N → ℝ)))
    (hfin : volume (V : Set (Fin N → ℝ)) < ⊤) {kk : ℕ} {u : (Fin N → ℝ) → ℝ}
    (hu : memSobolevXZero w Xt V kk P u) {D : List (Fin k) → (Fin N → ℝ) → ℝ}
    (hD : IsWeakJet w Xt V kk P u D) :
    ∃ φ : ℕ → TestFunction V ℝ (⊤ : ℕ∞),
      ConvLp V P (fun j => (φ j : (Fin N → ℝ) → ℝ)) u ∧ JetApprox w Xt V kk P D φ :=
  hD.exists_testSeq hXt hfin hu

/-- All letters of weight one: the weight of a word is its length. -/
theorem wordWeight_eq_length {w : Fin k → ℕ+} (hw : ∀ j, (w j : ℕ) = 1) (L : List (Fin k)) :
    wordWeight w L = L.length := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    simp only [wordWeight, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    rw [hw a, ih]
    omega

/-- The weak `X̃_J L̃ u = ∑ᵢ X̃_J X̃ᵢ² u` of a jet `D` without drift: `∑ᵢ D (J ++ [i, i])`
(for `J = []` this is the weak `L̃ u`). -/
def weakSumSquares (D : List (Fin k) → (Fin N → ℝ) → ℝ) (J : List (Fin k)) : (Fin N → ℝ) → ℝ :=
  fun x => ∑ i : Fin k, D (J ++ [i, i]) x

/-- The weak `L̃ u = X̃₀ u + ∑ᵢ X̃ᵢ² u` of a jet `D` of a drift alphabet `Fin (q + 1)`
(`D [0]` and `D [i.succ, i.succ]`). -/
def weakSumSquaresWithDrift {q : ℕ} (D : List (Fin (q + 1)) → (Fin N → ℝ) → ℝ) :
    (Fin N → ℝ) → ℝ :=
  fun x => D [0] x + ∑ i : Fin q, D [i.succ, i.succ] x

/-- A classical word derivative of a concatenated word. -/
theorem wordDerivative_append_apply (σ τ : List (Fin k)) (f : (Fin N → ℝ) → ℝ) :
    wordDerivative Xt (σ ++ τ) f = wordDerivative Xt σ (wordDerivative Xt τ f) := by
  induction σ with
  | nil => rfl
  | cons a σ ih => simp only [List.cons_append, wordDerivative, ih]

/-- The evaluation of a finite sum of test functions. -/
theorem coe_finset_sum_test {ι : Type*} (s : Finset ι) (t : ι → TestFunction V ℝ (⊤ : ℕ∞))
    (x : Fin N → ℝ) :
    ((∑ i ∈ s, t i : TestFunction V ℝ (⊤ : ℕ∞)) : (Fin N → ℝ) → ℝ) x = ∑ i ∈ s, t i x := by
  let ev : TestFunction V ℝ (⊤ : ℕ∞) →+ ℝ :=
    { toFun := fun φ => φ x, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have h := map_sum ev t s
  exact h

/-- Classical word derivatives are additive on finite sums of test functions. -/
theorem wordDerivative_finset_sum_test
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (V : Set (Fin N → ℝ))) {ι : Type*} (s : Finset ι)
    (t : ι → TestFunction V ℝ (⊤ : ℕ∞)) (J : List (Fin k)) :
    wordDerivative Xt J (fun y => ∑ i ∈ s, (t i : (Fin N → ℝ) → ℝ) y) =
      fun x => ∑ i ∈ s, wordDerivative Xt J (t i : (Fin N → ℝ) → ℝ) x := by
  induction J with
  | nil => rfl
  | cons j J ih =>
    funext x
    change fieldDerivative (Xt j) (wordDerivative Xt J (fun y => ∑ i ∈ s, (t i : _) y)) x =
      ∑ i ∈ s, fieldDerivative (Xt j) (wordDerivative Xt J (t i : (Fin N → ℝ) → ℝ)) x
    rw [ih]
    unfold fieldDerivative
    have hd : ∀ i ∈ s, DifferentiableAt ℝ (wordDerivative Xt J (t i : (Fin N → ℝ) → ℝ)) x :=
      fun i _ => ((S.wordDerivativeTest V Xt hXt J (t i)).contDiff.differentiable (by simp)).differentiableAt
    rw [fderiv_fun_sum hd, _root_.sum_apply]

/-- `X̃_J L̃ φ = ∑ᵢ X̃_{J ++ [i, i]} φ` of a test `φ` (no drift) as a test function. -/
def sumSquaresWordTest (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (V : Set (Fin N → ℝ)))
    (J : List (Fin k)) (φ : TestFunction V ℝ (⊤ : ℕ∞)) : TestFunction V ℝ (⊤ : ℕ∞) :=
  ∑ i : Fin k, S.wordDerivativeTest V Xt hXt (J ++ [i, i]) φ

/-- The values of `sumSquaresWordTest` are those of the classical `X̃_J (∑ᵢ X̃ᵢ² φ)`. -/
theorem coe_sumSquaresWordTest (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (V : Set (Fin N → ℝ)))
    (J : List (Fin k)) (φ : TestFunction V ℝ (⊤ : ℕ∞)) :
    (sumSquaresWordTest hXt J φ : (Fin N → ℝ) → ℝ) =
      wordDerivative Xt J (sumSquares Xt (φ : (Fin N → ℝ) → ℝ)) := by
  have h1 : sumSquares Xt (φ : (Fin N → ℝ) → ℝ) =
      fun y => ∑ i ∈ (Finset.univ : Finset (Fin k)),
        ((S.wordDerivativeTest V Xt hXt [i, i] φ : TestFunction V ℝ (⊤ : ℕ∞)) :
          (Fin N → ℝ) → ℝ) y := rfl
  rw [h1, wordDerivative_finset_sum_test hXt Finset.univ
    (fun i => S.wordDerivativeTest V Xt hXt [i, i] φ) J]
  funext x
  unfold sumSquaresWordTest
  rw [coe_finset_sum_test]
  refine Finset.sum_congr rfl fun i _ => ?_
  change wordDerivative Xt (J ++ [i, i]) (φ : (Fin N → ℝ) → ℝ) x =
    wordDerivative Xt J (wordDerivative Xt [i, i] (φ : (Fin N → ℝ) → ℝ)) x
  rw [wordDerivative_append_apply]

/-- Along tests approximating the jet, `X̃_J L̃ φ_j → X̃_J L̃ u`
(no drift, all weights one, `|J| + 2 ≤ kk`) in `L^P(V)`. -/
theorem JetApprox.convLp_sumSquares {w : Fin k → ℕ+}
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (V : Set (Fin N → ℝ)))
    (hw : ∀ j, (w j : ℕ) = 1) {kk : ℕ} {D : List (Fin k) → (Fin N → ℝ) → ℝ}
    {φ : ℕ → TestFunction V ℝ (⊤ : ℕ∞)} (h : JetApprox w Xt V kk P D φ) (J : List (Fin k))
    (hJ : J.length + 2 ≤ kk) :
    ConvLp V P (fun j => (sumSquaresWordTest hXt J (φ j) : (Fin N → ℝ) → ℝ))
      (weakSumSquares D J) := by
  have hmem : ∀ i : Fin k, J ++ [i, i] ∈ wordFamily w kk := fun i => by
    rw [S.mem_wordFamily_iff, wordWeight_eq_length hw]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have e : (fun j => (sumSquaresWordTest hXt J (φ j) : (Fin N → ℝ) → ℝ)) =
      fun j x => ∑ i ∈ (Finset.univ : Finset (Fin k)),
        wordDerivative Xt (J ++ [i, i]) (φ j : (Fin N → ℝ) → ℝ) x := by
    funext j x
    unfold sumSquaresWordTest
    rw [coe_finset_sum_test]
    rfl
  rw [e]
  exact ConvLp.finset_sum Finset.univ fun i _ => h _ (hmem i)

omit [Fact (1 ≤ P)] in
/-- **Weak jets are consistent with composition**: if `D τ` is the weak `X̃_τ`-derivative of
`u` and `D (J ++ τ)` that of the word `J ++ τ` (`X̃_J X̃_τ`), then `D (J ++ τ)` is the weak
`X̃_J`-derivative of the function `D τ`. -/
theorem IsWeakJet.hasWeakWordDeriv_append {w : Fin k → ℕ+}
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (V : Set (Fin N → ℝ))) {kk : ℕ}
    {u : (Fin N → ℝ) → ℝ} {D : List (Fin k) → (Fin N → ℝ) → ℝ}
    (hD : IsWeakJet w Xt V kk P u D) (τ : List (Fin k)) :
    ∀ J : List (Fin k), J ++ τ ∈ wordFamily w kk → hasWeakWordDeriv Xt V J (D τ) (D (J ++ τ))
  | [], h => S.hasWeakWordDeriv_nil Xt V (hD τ (by simpa using h)).1.2.1
  | j :: J', h => by
    have hm : J' ++ τ ∈ wordFamily w kk :=
      S.sublist_mem_wordFamily w kk
        (List.Sublist.append (List.sublist_cons_self j J') (List.Sublist.refl τ)) h
    have ih := IsWeakJet.hasWeakWordDeriv_append hXt hD τ J' hm
    have hu' := (hD (J' ++ τ) hm).1
    have hfull := (hD (j :: J' ++ τ) h).1
    have hone := (S.hasWeakWordDeriv_cons_iff Xt V hXt hu' j).mp hfull
    exact (S.hasWeakWordDeriv_cons_iff Xt V hXt ih j).mpr hone

omit [Fact (1 ≤ P)] in
/-- A weak jet of `u` is consistent with `L̃`: for `|J| + 2 ≤ kk` the weak `X̃_J`-derivative
of the weak `L̃ u = ∑ᵢ D [i, i]` is `∑ᵢ D (J ++ [i, i])`. -/
theorem IsWeakJet.hasWeakWordDeriv_sumSquares {w : Fin k → ℕ+}
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (V : Set (Fin N → ℝ)))
    (hw : ∀ j, (w j : ℕ) = 1) {kk : ℕ} {u : (Fin N → ℝ) → ℝ}
    {D : List (Fin k) → (Fin N → ℝ) → ℝ} (hD : IsWeakJet w Xt V kk P u D) (J : List (Fin k))
    (hJ : J.length + 2 ≤ kk) :
    hasWeakWordDeriv Xt V J (weakSumSquares D []) (weakSumSquares D J) := by
  classical
  have hmem' : ∀ i : Fin k, J ++ [i, i] ∈ wordFamily w kk := fun i => by
    rw [S.mem_wordFamily_iff, wordWeight_eq_length hw]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have hsum : ∀ (s : Finset (Fin k)),
      hasWeakWordDeriv Xt V J (fun x => ∑ i ∈ s, D ([] ++ [i, i]) x)
        (fun x => ∑ i ∈ s, D (J ++ [i, i]) x) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using S.hasWeakWordDeriv_zero Xt V J
    | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact S.hasWeakWordDeriv_add Xt V hXt (hD.hasWeakWordDeriv_append hXt [a, a] J (hmem' a)) ih
  exact hsum Finset.univ

end JetApprox

section Mul

variable {N k : ℕ} {Xt : Fin k → (Fin N → ℝ) → (Fin N → ℝ)} {V : Opens (Fin N → ℝ)}
  {P : ℝ≥0∞} [Fact (1 ≤ P)]

/-- **The weak extension limit for `a u`** (approximate
`u` in `W^{m,p}_0(V)` by tests; all right-hand inputs converge in `L^p`, all outputs converge by the
continuity theorem, and left-hand derivatives converge in distributions). Let `u ∈ W^{kk,P}_{X̃,0}(V)` with weak jet
`D`, `a ∈ C_c^∞(V)`. If `X̃_I (a φ) = R φ` weakly for every test `φ`, and `R φ_j → R₀` in `L^P(V)` along
every sequence of tests approximating the jet, then `X̃_I (a u) = R₀` weakly. -/
theorem weakExtension_mul {w : Fin k → ℕ+}
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (V : Set (Fin N → ℝ)))
    (hfin : volume (V : Set (Fin N → ℝ)) < ⊤) {kk : ℕ} {u : (Fin N → ℝ) → ℝ}
    (hu : memSobolevXZero w Xt V kk P u) {D : List (Fin k) → (Fin N → ℝ) → ℝ}
    (hD : IsWeakJet w Xt V kk P u D) (a : TestFunction V ℝ (⊤ : ℕ∞)) (I : List (Fin k))
    (R : TestFunction V ℝ (⊤ : ℕ∞) → (Fin N → ℝ) → ℝ) (R₀ : (Fin N → ℝ) → ℝ)
    (hR : ∀ φ : ℕ → TestFunction V ℝ (⊤ : ℕ∞), JetApprox w Xt V kk P D φ →
      ConvLp V P (fun j => R (φ j)) R₀)
    (h : ∀ φ : TestFunction V ℝ (⊤ : ℕ∞), hasWeakWordDeriv Xt V I (fun x => a x * φ x) (R φ)) :
    hasWeakWordDeriv Xt V I (fun x => a x * u x) R₀ := by
  obtain ⟨φ, hφu, hφ⟩ := exists_jetApprox hXt hfin hu hD
  exact hasWeakWordDeriv_of_convLp hXt I (hφu.mul_test a) (hR φ hφ) fun j => h (φ j)

/-- The a.e. form of `weakExtension_mul`: if `a φ = R φ` a.e. on `V` for
every test and `R φ_j → R₀` in `L^P(V)` along every approximating sequence, then `a u = R₀` a.e. -/
theorem weakExtension_mul_ae {w : Fin k → ℕ+}
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (V : Set (Fin N → ℝ)))
    (hfin : volume (V : Set (Fin N → ℝ)) < ⊤) {kk : ℕ} {u : (Fin N → ℝ) → ℝ}
    (hu : memSobolevXZero w Xt V kk P u) {D : List (Fin k) → (Fin N → ℝ) → ℝ}
    (hD : IsWeakJet w Xt V kk P u D) (a : TestFunction V ℝ (⊤ : ℕ∞))
    (R : TestFunction V ℝ (⊤ : ℕ∞) → (Fin N → ℝ) → ℝ) (R₀ : (Fin N → ℝ) → ℝ)
    (hR : ∀ φ : ℕ → TestFunction V ℝ (⊤ : ℕ∞), JetApprox w Xt V kk P D φ →
      ConvLp V P (fun j => R (φ j)) R₀)
    (h : ∀ φ : TestFunction V ℝ (⊤ : ℕ∞),
      (fun x => a x * φ x) =ᵐ[volume.restrict (V : Set (Fin N → ℝ))] R φ) :
    (fun x => a x * u x) =ᵐ[volume.restrict (V : Set (Fin N → ℝ))] R₀ := by
  obtain ⟨φ, hφu, hφ⟩ := exists_jetApprox hXt hfin hu hD
  exact (hφu.mul_test a).ae_eq_of_ae_eq (hR φ hφ) fun j => h (φ j)

end Mul

namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}
  {q : ℕ} {H : H1.StandingHypotheses C.G q} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)} {lam : ℕ} {P : ℝ≥0∞} [Fact (1 ≤ P)]

/-- **`L^P` convergence of tests gives convergence of the images**:
if tests `ψ_j → g` in `L^P(V)`, then `T ψ_j → T̄ g` in `L^P(V)` (by the continuity theorem, `T̄` is bounded and agrees with
`T` on tests). -/
theorem _root_.RothschildStein.P1.TypeOperator.convLp_apply (hF : C.IsStandardFrame F H K hQ)
    (T : TypeOperator F lam) (hP1 : 1 < P) (hP : P ≠ ⊤)
    {ψ : ℕ → TestFunction F.V ℝ (⊤ : ℕ∞)} {g : (Fin (n + m) → ℝ) → ℝ}
    (h : ConvLp F.V P (fun j => (ψ j : (Fin (n + m) → ℝ) → ℝ)) g) :
    ConvLp F.V P (fun j => T.apply (ψ j : (Fin (n + m) → ℝ) → ℝ)) (T.lpAct hF hP1 hP g) :=
  (h.lpAct hF T hP1 hP).congr_ae (fun j => T.lpAct_test hF hP1 hP (ψ j)) Filter.EventuallyEq.rfl

end LiftedChart

end RothschildStein.P1
