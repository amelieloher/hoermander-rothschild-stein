-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.GainWord
public import RothschildStein.S.WeakGraph
public import RothschildStein.S.Conjugate

/-!
# Gain: weak derivatives pass to the bounded extensions

The identity `X̃_I (T f) = S f` of weak derivatives holds on tests (`LeftDifferentiation.exists_wordOperator`).
"Pass derivative identities from tests by `L^p` approximation and continuity of distributional
differentiation" (proof of the gain theorem):

* `hasWeakWordDeriv_extension`: if bounded operators `T̄, S̄` on `L^P(V)` agree with `a f, b f` on tests
  and `X̃_I (a f) = b f` weakly for tests, then `X̃_I (T̄ g) = S̄ g` weakly for **every** `g ∈ L^P(V)`
  (the weak-derivative graph is closed in `L^P × L^P` and tests are dense);
* `TypeOperator.hasWeakWordDeriv_of_holder`: for a function `f` of finite Hölder norm the pointwise
  actions satisfy `X̃_I (T f) = S f` weakly on `V` (apply the previous statement at `P = 2` to `g = f`
  and use the agreement of the `L^2` extensions with the pointwise actions of the continuity theorem: "Hölder inputs
  belong to `L^p` on this finite-volume patch").
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal Topology
namespace RothschildStein.P1

section Closure

variable {N k : ℕ} {Xt : Fin k → (Fin N → ℝ) → (Fin N → ℝ)} {V : Opens (Fin N → ℝ)}

/-- **Weak derivatives pass to bounded `L^P` limits** (closedness of the weak-derivative
graph and density of tests): `T̄` and `S̄` bounded on `L^P(V)`, `1 ≤ P < ∞`, with `T̄ (f) = a f` and
`S̄ (f) = b f` a.e. on tests and `X̃_I (a f) = b f` weakly for tests `f`; then `X̃_I (T̄ g) = S̄ g`
weakly for every `g ∈ L^P(V)`. -/
theorem hasWeakWordDeriv_extension
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (V : Set (Fin N → ℝ)))
    (hfin : volume (V : Set (Fin N → ℝ)) < ⊤) {P : ℝ≥0∞} [Fact (1 ≤ P)] (hP : P ≠ ⊤)
    (I : List (Fin k))
    (a b : TestFunction V ℝ (⊤ : ℕ∞) → (Fin N → ℝ) → ℝ)
    (Tb Sb : Lp ℝ P (volume.restrict (V : Set (Fin N → ℝ))) →L[ℝ]
      Lp ℝ P (volume.restrict (V : Set (Fin N → ℝ))))
    (hT : ∀ f, Tb (testToLp V hfin P f) =ᵐ[volume.restrict (V : Set (Fin N → ℝ))] a f)
    (hS : ∀ f, Sb (testToLp V hfin P f) =ᵐ[volume.restrict (V : Set (Fin N → ℝ))] b f)
    (hab : ∀ f, hasWeakWordDeriv Xt V I (a f) (b f))
    (g : Lp ℝ P (volume.restrict (V : Set (Fin N → ℝ)))) :
    hasWeakWordDeriv Xt V I (Tb g) (Sb g) := by
  let r : ℝ≥0∞ := (1 - P⁻¹)⁻¹
  have : ENNReal.HolderConjugate P r := S.holderConjugate_complement P Fact.out
  have : Fact (1 ≤ r) := ⟨ENNReal.HolderConjugate.one_le r P⟩
  have hclosed := S.isClosed_weakWordGraph V Xt hXt I P r
  have hcont : Continuous (fun g : Lp ℝ P (volume.restrict (V : Set (Fin N → ℝ))) => (Tb g, Sb g)) :=
    Tb.continuous.prodMk Sb.continuous
  have hsub : Set.range (testToLp V hfin P) ⊆ (fun g : Lp ℝ P (volume.restrict
      (V : Set (Fin N → ℝ))) => (Tb g, Sb g)) ⁻¹'
      {v : Lp ℝ P (volume.restrict (V : Set (Fin N → ℝ))) ×
        Lp ℝ P (volume.restrict (V : Set (Fin N → ℝ))) | hasWeakWordDeriv Xt V I v.1 v.2} := by
    rintro _ ⟨f, rfl⟩
    exact S.hasWeakWordDeriv_congr_ae Xt V (hab f) (hT f).symm (hS f).symm
  have hdense := denseRange_testToLp V hfin hP
  have hg : g ∈ closure (Set.range (testToLp V hfin P)) := hdense.closure_eq ▸ Set.mem_univ g
  exact ((hclosed.preimage hcont).closure_subset_iff.mpr hsub) hg

end Closure

namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}
  {q : ℕ} {H : H1.StandingHypotheses C.G q} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)}

/-- **Weak derivatives of the actions on Hölder inputs.** If `X̃_I (T f) = S f` weakly on
`V` for every test `f`, then the same holds for every `f` of finite Hölder norm `‖f‖_{C^α(V)}`,
`0 < α < 1`, with the pointwise actions of the continuity theorem (integral/PV plus multiplier). -/
theorem _root_.RothschildStein.P1.TypeOperator.hasWeakWordDeriv_of_holder
    (hF : C.IsStandardFrame F H K hQ) {a b : ℕ} (T : TypeOperator F a) (U : TypeOperator F b)
    (I : List (Fin k))
    (h : ∀ f : TestFunction F.V ℝ (⊤ : ℕ∞), hasWeakWordDeriv C.Xl F.V I (T.apply f) (U.apply f))
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {f : (Fin (n + m) → ℝ) → ℝ}
    (hf : holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) f ≠ ⊤) :
    hasWeakWordDeriv C.Xl F.V I (T.apply f) (U.apply f) := by
  have : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨one_le_two⟩
  have hP1 : 1 < (2 : ℝ≥0∞) := by norm_num
  have hP : (2 : ℝ≥0∞) ≠ ⊤ := by simp
  obtain ⟨-, -, Tb, -, hTt, hTh, -⟩ := T.exists_lpExtension_standard hF hP1 hP
  obtain ⟨-, -, Sb, -, hSt, hSh, -⟩ := U.exists_lpExtension_standard hF hP1 hP
  have hfm : AEStronglyMeasurable f (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) :=
    aestronglyMeasurable_of_holderENorm_lt_top hF.lifted.subset_U F.V.isOpen.measurableSet hα0
      (lt_top_iff_ne_top.mpr hf)
  have hfin := hF.lifted.volume_lt_top
  have key := hasWeakWordDeriv_extension (Xt := C.Xl) hF.lifted.contDiffOn_Xl hfin hP I
    (fun f => T.apply f) (fun f => U.apply f) Tb Sb (fun f => (hTt f).2) (fun f => (hSt f).2) h
    ((memLp_of_holderENorm_ne_top F.V.isOpen.measurableSet hfin hf hfm 2).toLp f)
  exact RothschildStein.S.hasWeakWordDeriv_congr_ae C.Xl F.V key (hTh hα0 hα1 f hf hfm) (hSh hα0 hα1 f hf hfm)

end LiftedChart

end RothschildStein.P1
