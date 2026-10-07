-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.WeakExtensionJet
public import RothschildStein.P1.RepresentationFirstOrder

/-!
# The signed parametrix identities on `L^p(V)` and `W^{2,p}_{X̃,0}(V)`

The operator-level conclusion of the signed parametrix (`SignedParametrix`, BB pp. 560–564, Thm 11.25) is

* `M_a = L̃* P₁ + F₁` in the sense of distributions on tests: `∫ P₁ f · L̃φ = ∫ a f φ - ∫ F₁ f · φ`;
* `M_a = P₂ L̃ + F₂`: `a f = P₂ (L̃ f) + F₂ f` on `V` for tests `f`.

By the continuity theorem (`TypeOperator.lpAct`) both extend to
`u ∈ W^{2,p}_{X̃,0}(V)`, as identities in distributions and between the indicated `L^p` representatives:

* `weakExtension_parametrix_adjoint`: the first identity for every `g ∈ L^p(V)`, in particular for every
  `u ∈ W^{2,p}_{X̃,0}(V)`;
* `weakExtension_parametrix_left`: `a u = P̄₂ (L̃ u) + F̄₂ u` a.e. on `V` for `u ∈ W^{2,p}_{X̃,0}(V)` (here
  `L̃ u` is the weak `L̃`, `weakSumSquaresWithDrift`), the `L^p` representatives of the sides
  (`weakExtension_parametrix_left_drift`);
* `weakExtension_parametrix_full_of` (`WeakExtensionMain`): the conclusion of `SignedParametrix` together
  with both extensions.

Nothing here regularizes an arbitrary distribution: all inputs are in the closure of the tests.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal Topology
namespace RothschildStein.P1

section Generic

variable {N k : ℕ} {Xt : Fin k → (Fin N → ℝ) → (Fin N → ℝ)} {V : Opens (Fin N → ℝ)}
  {P : ℝ≥0∞} [Fact (1 ≤ P)] {w : Fin k → ℕ+}

/-- Along tests approximating the jet of `u`, the tests converge to `u`. -/
theorem JetApprox.convLp_nil {kk : ℕ} {u : (Fin N → ℝ) → ℝ} {D : List (Fin k) → (Fin N → ℝ) → ℝ}
    {φ : ℕ → TestFunction V ℝ (⊤ : ℕ∞)} (h : JetApprox w Xt V kk P D φ)
    (hD : IsWeakJet w Xt V kk P u D) : ConvLp V P (fun j => (φ j : (Fin N → ℝ) → ℝ)) u :=
  (h [] (S.nil_mem_wordFamily w kk)).congr_ae (fun _ => Filter.EventuallyEq.rfl) hD.nil_ae

end Generic

section GenericDrift

variable {N q : ℕ} {Xt : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)} {V : Opens (Fin N → ℝ)}
  {P : ℝ≥0∞} [Fact (1 ≤ P)] {w : Fin (q + 1) → ℕ+}

/-- `X̃₀` and `X̃ᵢ²` are words of weight two (drift weight `2`, horizontal
weight `1`), hence entries of every jet of order `2`. -/
theorem drift_words_mem_wordFamily (hw0 : (w 0 : ℕ) = 2) (hw : ∀ j : Fin q, (w j.succ : ℕ) = 1) :
    ([0] ∈ wordFamily w 2) ∧ ∀ i : Fin q, ([i.succ, i.succ] ∈ wordFamily w 2) := by
  refine ⟨(S.mem_wordFamily_iff w 2 [0]).2 (by simp [wordWeight, hw0]), fun i => ?_⟩
  exact (S.mem_wordFamily_iff w 2 _).2 (by simp [wordWeight, hw i])

/-- Along tests approximating the jet, `L̃ φ_j → L̃ u` in `L^P(V)`
(`L̃ = X̃₀ + ∑ᵢ X̃ᵢ²`; the limit is the weak `L̃ u`, `weakSumSquaresWithDrift`). -/
theorem JetApprox.convLp_sumSquaresWithDrift
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (V : Set (Fin N → ℝ)))
    (hw0 : (w 0 : ℕ) = 2) (hw : ∀ j : Fin q, (w j.succ : ℕ) = 1)
    {D : List (Fin (q + 1)) → (Fin N → ℝ) → ℝ} {φ : ℕ → TestFunction V ℝ (⊤ : ℕ∞)}
    (h : JetApprox w Xt V 2 P D φ) :
    ConvLp V P (fun j => (sumSquaresWithDriftTest V Xt hXt (φ j) : (Fin N → ℝ) → ℝ))
      (weakSumSquaresWithDrift D) := by
  obtain ⟨h0, hi⟩ := drift_words_mem_wordFamily (w := w) hw0 hw
  have e : (fun j => (sumSquaresWithDriftTest V Xt hXt (φ j) : (Fin N → ℝ) → ℝ)) =
      fun j x => wordDerivative Xt [0] (φ j : (Fin N → ℝ) → ℝ) x +
        ∑ i : Fin q, wordDerivative Xt [i.succ, i.succ] (φ j : (Fin N → ℝ) → ℝ) x := by
    funext j
    rw [sumSquaresWithDriftTest_coe]
    rfl
  rw [e]
  exact (h [0] h0).add (ConvLp.finset_sum Finset.univ fun i _ => h [i.succ, i.succ] (hi i))

end GenericDrift

namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}
  {r : ℕ} {H : H1.StandingHypotheses C.G r} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)} {P : ℝ≥0∞} [Fact (1 ≤ P)]

/-- **The first parametrix identity on `L^p(V)`.** Let `P₁` (type 2) and `F₁` (type 1) satisfy
`∫ P₁ f · L̃φ = ∫ a f φ - ∫ F₁ f · φ` for tests `f, φ` (the distributional identity `M_a = L̃* P₁ + F₁` of
`SignedParametrixOf`, `L̃ = Lt` mapping tests to tests). Then
`∫ P̄₁ g · L̃φ = ∫ a g φ - ∫ F̄₁ g · φ` for every `g ∈ L^P(V)`, `1 < P < ∞`, in particular for every
`g = u ∈ W^{2,P}_{X̃,0}(V)`. -/
theorem weakExtension_parametrix_adjoint (hF : C.IsStandardFrame F H K hQ)
    {Lt : ((Fin (n + m) → ℝ) → ℝ) → (Fin (n + m) → ℝ) → ℝ}
    (Lap : TestFunction F.V ℝ (⊤ : ℕ∞) → TestFunction F.V ℝ (⊤ : ℕ∞))
    (hLap : ∀ u, (Lap u : (Fin (n + m) → ℝ) → ℝ) = Lt u) {a : TestFunction F.V ℝ (⊤ : ℕ∞)}
    {P₁ : TypeOperator F 2} {F₁ : TypeOperator F 1}
    (hadj : ∀ f φ : TestFunction F.V ℝ (⊤ : ℕ∞),
      (∫ ξ in (F.V : Set (Fin (n + m) → ℝ)), P₁.apply f ξ * Lt φ ξ) =
        (∫ ξ in (F.V : Set (Fin (n + m) → ℝ)), a ξ * f ξ * φ ξ) -
          ∫ ξ in (F.V : Set (Fin (n + m) → ℝ)), F₁.apply f ξ * φ ξ)
    (hP1 : 1 < P) (hP : P ≠ ⊤) {g : (Fin (n + m) → ℝ) → ℝ}
    (hg : MemLp g P (volume.restrict (F.V : Set (Fin (n + m) → ℝ))))
    (φ : TestFunction F.V ℝ (⊤ : ℕ∞)) :
    (∫ ξ in (F.V : Set (Fin (n + m) → ℝ)), P₁.lpAct hF hP1 hP g ξ * Lt φ ξ) =
      (∫ ξ in (F.V : Set (Fin (n + m) → ℝ)), a ξ * g ξ * φ ξ) -
        ∫ ξ in (F.V : Set (Fin (n + m) → ℝ)), F₁.lpAct hF hP1 hP g ξ * φ ξ := by
  obtain ⟨ψ, hψ⟩ := exists_testSeq_convLp hF.lifted.volume_lt_top hP hg
  have h1 := (P₁.convLp_apply hF hP1 hP hψ).tendsto_integral_mul_test (Lap φ)
  have h2 := (hψ.mul_test a).tendsto_integral_mul_test φ
  have h3 := (F₁.convLp_apply hF hP1 hP hψ).tendsto_integral_mul_test φ
  have e1 : ∀ j, (∫ x in (F.V : Set (Fin (n + m) → ℝ)),
      P₁.apply (ψ j : (Fin (n + m) → ℝ) → ℝ) x * (Lap φ : (Fin (n + m) → ℝ) → ℝ) x) =
      (∫ x in (F.V : Set (Fin (n + m) → ℝ)), a x * ψ j x * φ x) -
        ∫ x in (F.V : Set (Fin (n + m) → ℝ)),
          F₁.apply (ψ j : (Fin (n + m) → ℝ) → ℝ) x * φ x := fun j => by
    rw [hLap φ]
    exact hadj (ψ j) φ
  have key := tendsto_nhds_unique (h1.congr e1) (h2.sub h3)
  rw [hLap φ] at key
  exact key

/-- **The second parametrix identity on `W^{2,P}_{X̃,0}(V)`**: `a u = P̄₂ (L̃ u) + F̄₂ u` a.e. on
`V`. Let `a f = P₂ (L̃ f) + F₂ f` on `V` for tests `f` (`L̃ = Lt`, `Lap` the same operator on tests),
`u ∈ W^{kk,P}_{X̃,0}(V)` (`memSobolevXZero`) with weak jet `D`, and `LD` the `L^P` limit of
`L̃ φ_j` along every sequence of tests approximating the jet (for the lifted `L̃` this is the weak
`L̃ u`, `weakSumSquaresWithDrift`). Then the `L^P` representatives satisfy
`a u = P̄₂ LD + F̄₂ u` almost everywhere on `V`. -/
theorem weakExtension_parametrix_left (hF : C.IsStandardFrame F H K hQ)
    {Lt : ((Fin (n + m) → ℝ) → ℝ) → (Fin (n + m) → ℝ) → ℝ}
    (Lap : TestFunction F.V ℝ (⊤ : ℕ∞) → TestFunction F.V ℝ (⊤ : ℕ∞))
    (hLap : ∀ u, (Lap u : (Fin (n + m) → ℝ) → ℝ) = Lt u) {a : TestFunction F.V ℝ (⊤ : ℕ∞)}
    {P₂ : TypeOperator F 2} {F₂ : TypeOperator F 1}
    (hzero : ∀ f : TestFunction F.V ℝ (⊤ : ℕ∞), ∀ ξ ∈ (F.V : Set (Fin (n + m) → ℝ)),
      a ξ * f ξ = P₂.apply (Lt f) ξ + F₂.apply f ξ)
    (hP1 : 1 < P) (hP : P ≠ ⊤) {kk : ℕ} {u : (Fin (n + m) → ℝ) → ℝ}
    (hu : memSobolevXZero w C.Xl F.V kk P u) {D : List (Fin k) → (Fin (n + m) → ℝ) → ℝ}
    (hD : IsWeakJet w C.Xl F.V kk P u D) {LD : (Fin (n + m) → ℝ) → ℝ}
    (hLD : ∀ φ : ℕ → TestFunction F.V ℝ (⊤ : ℕ∞), JetApprox w C.Xl F.V kk P D φ →
      ConvLp F.V P (fun j => (Lap (φ j) : (Fin (n + m) → ℝ) → ℝ)) LD) :
    (fun x => a x * u x) =ᵐ[volume.restrict (F.V : Set (Fin (n + m) → ℝ))]
      fun ξ => P₂.lpAct hF hP1 hP LD ξ + F₂.lpAct hF hP1 hP u ξ := by
  refine weakExtension_mul_ae hF.lifted.contDiffOn_Xl hF.lifted.volume_lt_top hu hD a
    (fun f ξ => P₂.apply (Lt f) ξ + F₂.apply f ξ) _ (fun φ hφ => ?_) (fun f => ?_)
  · have h1 := P₂.convLp_apply hF hP1 hP (hLD φ hφ)
    simp only [hLap] at h1
    exact h1.add (F₂.convLp_apply hF hP1 hP (hφ.convLp_nil hD))
  · exact (ae_restrict_iff' F.V.isOpen.measurableSet).2
      (Filter.Eventually.of_forall fun ξ hξ => hzero f ξ hξ)

end LiftedChart

namespace LiftedChart

variable {n q : ℕ} {w : Fin (q + 1) → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}
  {r : ℕ} {H : H1.StandingHypotheses C.G r} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)} {P : ℝ≥0∞} [Fact (1 ≤ P)]

/-- **The second parametrix identity for the lifted `L̃ = X̃₀ + ∑ᵢ X̃ᵢ²`**: if
`a f = P₂ (L̃ f) + F₂ f` on `V` for tests `f`, then for `u ∈ W^{2,P}_{X̃,0}(V)` with weak jet `D`,
`a u = P̄₂ (L̃ u) + F̄₂ u` a.e. on `V`, `L̃ u = D [0] + ∑ᵢ D [i, i]` (the weak `L̃ u`) and `P̄₂, F̄₂` the
`L^P` extensions of `P₂, F₂` (continuity theorem). -/
theorem weakExtension_parametrix_left_drift (hF : C.IsStandardFrame F H K hQ)
    (hw0 : (w 0 : ℕ) = 2) (hw : ∀ j : Fin q, (w j.succ : ℕ) = 1)
    {a : TestFunction F.V ℝ (⊤ : ℕ∞)} {P₂ : TypeOperator F 2} {F₂ : TypeOperator F 1}
    (hzero : ∀ f : TestFunction F.V ℝ (⊤ : ℕ∞), ∀ ξ ∈ (F.V : Set (Fin (n + m) → ℝ)),
      a ξ * f ξ = P₂.apply (sumSquaresWithDrift C.Xl f) ξ + F₂.apply f ξ)
    (hP1 : 1 < P) (hP : P ≠ ⊤) {u : (Fin (n + m) → ℝ) → ℝ}
    (hu : memSobolevXZero w C.Xl F.V 2 P u) {D : List (Fin (q + 1)) → (Fin (n + m) → ℝ) → ℝ}
    (hD : IsWeakJet w C.Xl F.V 2 P u D) :
    (fun x => a x * u x) =ᵐ[volume.restrict (F.V : Set (Fin (n + m) → ℝ))]
      fun ξ => P₂.lpAct hF hP1 hP (weakSumSquaresWithDrift D) ξ + F₂.lpAct hF hP1 hP u ξ :=
  weakExtension_parametrix_left hF (sumSquaresWithDriftTest F.V C.Xl hF.lifted.contDiffOn_Xl)
    (fun u => sumSquaresWithDriftTest_coe F.V C.Xl hF.lifted.contDiffOn_Xl u) hzero hP1 hP hu hD
    (fun _ hφ => hφ.convLp_sumSquaresWithDrift hF.lifted.contDiffOn_Xl hw0 hw)

end LiftedChart

end RothschildStein.P1
