-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.GainExtension
public import RothschildStein.P1.ContinuityTheoremHolder
public import RothschildStein.S.SobolevRepresentatives
public import RothschildStein.S.SobolevZeroAE
public import RothschildStein.S.WeakSub
public import RothschildStein.S.TestPairing

/-!
# Weak extension: passing identities on tests to `W^{k,p}_{X̃,0}(V)`

An abstract form of the argument: approximate `u` in `W^{m,p}_0(V)` by tests; the right-hand inputs
converge in `L^p`, the outputs converge by the continuity theorem, and the left-hand derivatives
converge in distributions.

* `ConvLp V P f g`: `f j → g` in `L^P(V)` (`1 ≤ P`), with a calculus (sums, constant multiples,
  bounded multipliers, bounded `L^P` operators `actLp`, a.e. changes).
* `IsWeakJet`: a family `D` of `L^P` weak word derivatives of `u` for the words of weight at most `kk`.
* `exists_testSeq_convLp_jet` (BB Thm 2.9): `u ∈ W^{kk,P}_{X̃,0}(V)` is the limit of tests `φ_j` whose classical
  word derivatives converge in `L^P(V)` to the weak jet.
* `hasWeakWordDeriv_of_convLp` (closedness of the weak-derivative graph): `L^P` limits of weak
  derivative pairs are weak derivative pairs.
* `weakExtension_limit`, `weakExtension_limit_ae`: if `L φ`, `R φ` converge in `L^P` along every
  approximating sequence of tests, to `L₀, R₀`, and `X̃_I (L φ) = R φ` weakly (respectively
  `L φ = R φ` a.e.) for every test `φ`, then `X̃_I L₀ = R₀` weakly (a.e.). This is the shape in which
  every parametrix and representation identity is passed to the closure of the tests; it does **not** assert any
  regularity for an arbitrary distribution (BB pp. 564–568; the closure `W^{k,P}_{X̃,0}(V)` is the
  `memSobolevXZero`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal Topology
namespace RothschildStein.P1

section ConvLp

variable {N : ℕ} {V : Opens (Fin N → ℝ)} {P : ℝ≥0∞} [Fact (1 ≤ P)]

/-- `f j → g` in `L^P(V)`: every `f j` and `g` lie in `L^P(V)` and
the images in `L^P(V)` converge. -/
def ConvLp (V : Opens (Fin N → ℝ)) (P : ℝ≥0∞) [Fact (1 ≤ P)] (f : ℕ → (Fin N → ℝ) → ℝ)
    (g : (Fin N → ℝ) → ℝ) : Prop :=
  ∃ (hf : ∀ j, MemLp (f j) P (volume.restrict (V : Set (Fin N → ℝ))))
    (hg : MemLp g P (volume.restrict (V : Set (Fin N → ℝ)))),
    Tendsto (fun j => (hf j).toLp (f j)) atTop (𝓝 (hg.toLp g))

/-- `ConvLp` in terms of the `L^P(V)` distance. -/
theorem convLp_iff {f : ℕ → (Fin N → ℝ) → ℝ} {g : (Fin N → ℝ) → ℝ} :
    ConvLp V P f g ↔ (∀ j, MemLp (f j) P (volume.restrict (V : Set (Fin N → ℝ)))) ∧
      MemLp g P (volume.restrict (V : Set (Fin N → ℝ))) ∧
      Tendsto (fun j => eLpNorm (fun x => f j x - g x) P
        (volume.restrict (V : Set (Fin N → ℝ)))) atTop (𝓝 0) := by
  constructor
  · rintro ⟨hf, hg, h⟩
    exact ⟨hf, hg, (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf g hg).1 h⟩
  · rintro ⟨hf, hg, h⟩
    exact ⟨hf, hg, (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf g hg).2 h⟩

variable {f f' : ℕ → (Fin N → ℝ) → ℝ} {g g' : (Fin N → ℝ) → ℝ}

/-- The limit does not depend on representatives. -/
theorem ConvLp.congr_ae (h : ConvLp V P f g)
    (hf : ∀ j, f j =ᵐ[volume.restrict (V : Set (Fin N → ℝ))] f' j)
    (hg : g =ᵐ[volume.restrict (V : Set (Fin N → ℝ))] g') : ConvLp V P f' g' := by
  obtain ⟨hfm, hgm, ht⟩ := h
  have hfm' : ∀ j, MemLp (f' j) P (volume.restrict (V : Set (Fin N → ℝ))) :=
    fun j => (hfm j).ae_eq (hf j)
  have hgm' : MemLp g' P (volume.restrict (V : Set (Fin N → ℝ))) := hgm.ae_eq hg
  refine ⟨hfm', hgm', ?_⟩
  have e1 : ∀ j, (hfm' j).toLp (f' j) = (hfm j).toLp (f j) :=
    fun j => MemLp.toLp_congr _ _ (hf j).symm
  have e2 : hgm'.toLp g' = hgm.toLp g := MemLp.toLp_congr _ _ hg.symm
  simpa only [e1, e2] using ht

/-- Limits in `L^P(V)` are unique almost everywhere. -/
theorem ConvLp.ae_eq_of_ae_eq (h : ConvLp V P f g) (h' : ConvLp V P f' g')
    (hff : ∀ j, f j =ᵐ[volume.restrict (V : Set (Fin N → ℝ))] f' j) :
    g =ᵐ[volume.restrict (V : Set (Fin N → ℝ))] g' := by
  have h2 := h.congr_ae hff Filter.EventuallyEq.rfl
  obtain ⟨hf2, hg2, ht2⟩ := h2
  obtain ⟨hf3, hg3, ht3⟩ := h'
  have hfe : hf2 = hf3 := Subsingleton.elim _ _
  subst hfe
  exact (MemLp.toLp_eq_toLp_iff hg2 hg3).1 (tendsto_nhds_unique ht2 ht3)

/-- The constant sequence converges. -/
theorem ConvLp.const (hg : MemLp g P (volume.restrict (V : Set (Fin N → ℝ)))) :
    ConvLp V P (fun _ => g) g :=
  ⟨fun _ => hg, hg, tendsto_const_nhds⟩

/-- Sums of convergent sequences converge. -/
theorem ConvLp.add (h : ConvLp V P f g) (h' : ConvLp V P f' g') :
    ConvLp V P (fun j x => f j x + f' j x) (fun x => g x + g' x) := by
  obtain ⟨hfm, hgm, ht⟩ := h
  obtain ⟨hfm', hgm', ht'⟩ := h'
  refine ⟨fun j => (hfm j).add (hfm' j), hgm.add hgm', ?_⟩
  exact ht.add ht'

/-- The zero sequence converges to zero. -/
theorem ConvLp.zero : ConvLp V P (fun _ _ => (0 : ℝ)) (fun _ => (0 : ℝ)) :=
  ConvLp.const MemLp.zero

/-- Finite sums of convergent sequences converge. -/
theorem ConvLp.finset_sum {ι : Type*} (s : Finset ι) {F : ι → ℕ → (Fin N → ℝ) → ℝ}
    {G : ι → (Fin N → ℝ) → ℝ} (h : ∀ i ∈ s, ConvLp V P (F i) (G i)) :
    ConvLp V P (fun j x => ∑ i ∈ s, F i j x) (fun x => ∑ i ∈ s, G i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (ConvLp.zero (V := V) (P := P))
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- Multiplication by a fixed bounded measurable function preserves
`L^P` convergence (the multiplier term of a type-0 operator, the cutoff `a`). -/
theorem ConvLp.mul_bounded {b : (Fin N → ℝ) → ℝ} {M : ℝ}
    (hb : AEStronglyMeasurable b (volume.restrict (V : Set (Fin N → ℝ)))) (hM : ∀ x, |b x| ≤ M)
    (h : ConvLp V P f g) : ConvLp V P (fun j x => b x * f j x) (fun x => b x * g x) := by
  obtain ⟨hf, hg, ht⟩ := convLp_iff.1 h
  refine convLp_iff.2 ⟨fun j => (memLp_mul_of_bound hb hM (hf j)).1,
    (memLp_mul_of_bound hb hM hg).1, ?_⟩
  have hdiff : ∀ j, MemLp (fun x => f j x - g x) P (volume.restrict (V : Set (Fin N → ℝ))) :=
    fun j => (hf j).sub hg
  have h2 : Tendsto (fun j => ENNReal.ofReal M * eLpNorm (fun x => f j x - g x) P
      (volume.restrict (V : Set (Fin N → ℝ)))) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul ht (Or.inr ENNReal.ofReal_ne_top)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2 (fun _ => bot_le)
    (fun j => ?_)
  have e : (fun x => b x * f j x - b x * g x) = fun x => b x * (f j x - g x) := by
    funext x; ring
  rw [e]
  exact (memLp_mul_of_bound hb hM (hdiff j)).2

end ConvLp

section Act

variable {N : ℕ} {V : Opens (Fin N → ℝ)} {P : ℝ≥0∞} [Fact (1 ≤ P)]

open Classical in
/-- The action of a bounded operator `Tb` on `L^P(V)` on functions:
`Tb g` as a function when `g ∈ L^P(V)`, and `0` otherwise. -/
def actLp (Tb : Lp ℝ P (volume.restrict (V : Set (Fin N → ℝ))) →L[ℝ]
    Lp ℝ P (volume.restrict (V : Set (Fin N → ℝ)))) (g : (Fin N → ℝ) → ℝ) : (Fin N → ℝ) → ℝ :=
  if h : MemLp g P (volume.restrict (V : Set (Fin N → ℝ))) then ⇑(Tb (h.toLp g)) else 0

/-- On `L^P` inputs `actLp` is the operator. -/
theorem actLp_eq (Tb : Lp ℝ P (volume.restrict (V : Set (Fin N → ℝ))) →L[ℝ]
    Lp ℝ P (volume.restrict (V : Set (Fin N → ℝ)))) {g : (Fin N → ℝ) → ℝ}
    (hg : MemLp g P (volume.restrict (V : Set (Fin N → ℝ)))) : actLp Tb g = ⇑(Tb (hg.toLp g)) := by
  simp only [actLp, hg, ↓reduceDIte]

/-- `actLp` of an `L^P` function is in `L^P`. -/
theorem memLp_actLp (Tb : Lp ℝ P (volume.restrict (V : Set (Fin N → ℝ))) →L[ℝ]
    Lp ℝ P (volume.restrict (V : Set (Fin N → ℝ)))) {g : (Fin N → ℝ) → ℝ}
    (hg : MemLp g P (volume.restrict (V : Set (Fin N → ℝ)))) :
    MemLp (actLp Tb g) P (volume.restrict (V : Set (Fin N → ℝ))) := by
  rw [actLp_eq Tb hg]
  exact Lp.memLp _

/-- **Bounded operators on `L^P` preserve `L^P` convergence.** -/
theorem ConvLp.actLp {f : ℕ → (Fin N → ℝ) → ℝ} {g : (Fin N → ℝ) → ℝ}
    (Tb : Lp ℝ P (volume.restrict (V : Set (Fin N → ℝ))) →L[ℝ]
      Lp ℝ P (volume.restrict (V : Set (Fin N → ℝ)))) (h : ConvLp V P f g) :
    ConvLp V P (fun j => RothschildStein.P1.actLp Tb (f j)) (RothschildStein.P1.actLp Tb g) := by
  obtain ⟨hf, hg, ht⟩ := h
  refine ⟨fun j => memLp_actLp Tb (hf j), memLp_actLp Tb hg, ?_⟩
  have h1 := (Tb.continuous.tendsto _).comp ht
  have e : ∀ (u : (Fin N → ℝ) → ℝ) (hu : MemLp u P (volume.restrict (V : Set (Fin N → ℝ)))),
      (memLp_actLp Tb hu).toLp (RothschildStein.P1.actLp Tb u) = Tb (hu.toLp u) := by
    intro u hu
    simp only [actLp_eq Tb hu]
    exact Lp.toLp_coeFn _ _
  have h2 : Tendsto (fun j => (memLp_actLp Tb (hf j)).toLp (RothschildStein.P1.actLp Tb (f j)))
      atTop (𝓝 (Tb (hg.toLp g))) := h1.congr (fun j => (e (f j) (hf j)).symm)
  rw [e g hg]
  exact h2

end Act

section Jets

variable {N k : ℕ} {Xt : Fin k → (Fin N → ℝ) → (Fin N → ℝ)} {V : Opens (Fin N → ℝ)}
  {P : ℝ≥0∞} [Fact (1 ≤ P)]

/-- `D` is a family of `L^P(V)` weak word derivatives of `u` on `V` for
all words of weight at most `kk` (`D K` is one representative of the weak `X̃_K`-derivative of `u`);
the existence for `u` in `memSobolevX` is `IsWeakJet.exists`. -/
def IsWeakJet (w : Fin k → ℕ+) (Xt : Fin k → (Fin N → ℝ) → (Fin N → ℝ)) (V : Opens (Fin N → ℝ))
    (kk : ℕ) (P : ℝ≥0∞) (u : (Fin N → ℝ) → ℝ) (D : List (Fin k) → (Fin N → ℝ) → ℝ) : Prop :=
  ∀ K ∈ wordFamily w kk, hasWeakWordDeriv Xt V K u (D K) ∧
    MemLp (D K) P (volume.restrict (V : Set (Fin N → ℝ)))

/-- Every member of `W^{kk,P}_{X̃}(V)` has a weak jet (BB Thm 2.9). -/
theorem IsWeakJet.exists {w : Fin k → ℕ+} {kk : ℕ} {u : (Fin N → ℝ) → ℝ}
    (hu : memSobolevX w Xt V kk P u) : ∃ D, IsWeakJet w Xt V kk P u D := by
  obtain ⟨jet, -, h⟩ := S.exists_sobolev_representatives w Xt V kk hu
  exact ⟨jet, h⟩

omit [Fact (1 ≤ P)] in
/-- The empty-word entry of a weak jet represents `u`. -/
theorem IsWeakJet.nil_ae {w : Fin k → ℕ+} {kk : ℕ} {u : (Fin N → ℝ) → ℝ}
    {D : List (Fin k) → (Fin N → ℝ) → ℝ} (hD : IsWeakJet w Xt V kk P u D) :
    D [] =ᵐ[volume.restrict (V : Set (Fin N → ℝ))] u := by
  have h := hD [] (S.nil_mem_wordFamily w kk)
  exact S.hasWeakWordDeriv_unique Xt V h.1 (S.hasWeakWordDeriv_nil Xt V h.1.1)

omit [Fact (1 ≤ P)] in
/-- A word derivative of a test function lies in `L^P(V)`
(`V` of finite measure). -/
theorem memLp_wordDerivative_test (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (V : Set (Fin N → ℝ)))
    (hfin : volume (V : Set (Fin N → ℝ)) < ⊤) (K : List (Fin k))
    (φ : TestFunction V ℝ (⊤ : ℕ∞)) :
    MemLp (wordDerivative Xt K (φ : (Fin N → ℝ) → ℝ)) P (volume.restrict (V : Set (Fin N → ℝ))) :=
  testFunction_memLp V hfin (S.wordDerivativeTest V Xt hXt K φ) P

/-- **Approximation in jet form (BB Thm 2.9).** For `u` in
`W^{kk,P}_{X̃,0}(V)` (`memSobolevXZero`, `1 ≤ P`) with weak jet `D` there are tests `φ_j` with
`X̃_K φ_j → D K` in `L^P(V)` for every word `K` of weight at most `kk`; for the empty word,
`φ_j → u`. -/
theorem exists_testSeq_convLp_jet {w : Fin k → ℕ+}
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (V : Set (Fin N → ℝ)))
    (hfin : volume (V : Set (Fin N → ℝ)) < ⊤) {kk : ℕ} {u : (Fin N → ℝ) → ℝ}
    (hu : memSobolevXZero w Xt V kk P u) {D : List (Fin k) → (Fin N → ℝ) → ℝ}
    (hD : IsWeakJet w Xt V kk P u D) :
    ∃ φ : ℕ → TestFunction V ℝ (⊤ : ℕ∞), ∀ K ∈ wordFamily w kk,
      ConvLp V P (fun j => wordDerivative Xt K (φ j : (Fin N → ℝ) → ℝ)) (D K) := by
  obtain ⟨-, φ, hφ⟩ := hu
  refine ⟨φ, fun K hK => convLp_iff.2 ⟨fun j => memLp_wordDerivative_test hXt hfin K (φ j),
    (hD K hK).2, ?_⟩⟩
  have hw : ∀ j, hasWeakWordDeriv Xt V K (fun x => u x - φ j x)
      (fun x => D K x - wordDerivative Xt K (φ j : (Fin N → ℝ) → ℝ) x) := fun j =>
    S.hasWeakWordDeriv_sub Xt V hXt (hD K hK).1
      (S.hasWeakWordDeriv_classical V Xt hXt K (φ j : (Fin N → ℝ) → ℝ)
        (φ j).contDiff.contDiffOn)
  have hle : ∀ j, eLpNorm (fun x => wordDerivative Xt K (φ j : (Fin N → ℝ) → ℝ) x - D K x) P
      (volume.restrict (V : Set (Fin N → ℝ))) ≤
      sobolevXENorm w Xt V kk P (fun x => u x - φ j x) := fun j => by
    have h1 : eLpNorm (fun x => wordDerivative Xt K (φ j : (Fin N → ℝ) → ℝ) x - D K x) P
        (volume.restrict (V : Set (Fin N → ℝ))) =
        eLpNorm (fun x => D K x - wordDerivative Xt K (φ j : (Fin N → ℝ) → ℝ) x) P
          (volume.restrict (V : Set (Fin N → ℝ))) :=
      eLpNorm_sub_comm (fun x => wordDerivative Xt K (φ j : (Fin N → ℝ) → ℝ) x)
        (fun x => D K x) P _
    rw [h1, ← S.weakWordENorm_eq Xt V K P _ _ (hw j)]
    exact Finset.single_le_sum (f := fun I => weakWordENorm Xt V I P (fun x => u x - φ j x))
      (fun _ _ => bot_le) hK
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hφ (fun _ => bot_le) hle

/-- For `u` in the closure `W^{kk,P}_{X̃,0}(V)` of the tests and every
weak jet `D`, there is one sequence of tests approximating all entries of the jet at once. -/
theorem IsWeakJet.exists_testSeq {w : Fin k → ℕ+}
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (V : Set (Fin N → ℝ)))
    (hfin : volume (V : Set (Fin N → ℝ)) < ⊤) {kk : ℕ} {u : (Fin N → ℝ) → ℝ}
    (hu : memSobolevXZero w Xt V kk P u) {D : List (Fin k) → (Fin N → ℝ) → ℝ}
    (hD : IsWeakJet w Xt V kk P u D) :
    ∃ φ : ℕ → TestFunction V ℝ (⊤ : ℕ∞),
      ConvLp V P (fun j => (φ j : (Fin N → ℝ) → ℝ)) u ∧ ∀ K ∈ wordFamily w kk,
      ConvLp V P (fun j => wordDerivative Xt K (φ j : (Fin N → ℝ) → ℝ)) (D K) := by
  obtain ⟨φ, hφ⟩ := exists_testSeq_convLp_jet hXt hfin hu hD
  exact ⟨φ, (hφ [] (S.nil_mem_wordFamily w kk)).congr_ae (fun _ => Filter.EventuallyEq.rfl)
    hD.nil_ae, hφ⟩

end Jets

section Limit

variable {N k : ℕ} {Xt : Fin k → (Fin N → ℝ) → (Fin N → ℝ)} {V : Opens (Fin N → ℝ)}
  {P : ℝ≥0∞} [Fact (1 ≤ P)]

/-- **Weak word derivatives pass to `L^P` limits** (the graph of
the weak derivative is closed in `L^P × L^P`). -/
theorem hasWeakWordDeriv_of_convLp
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (V : Set (Fin N → ℝ))) (I : List (Fin k))
    {f g : ℕ → (Fin N → ℝ) → ℝ} {f₀ g₀ : (Fin N → ℝ) → ℝ}
    (hf : ConvLp V P f f₀) (hg : ConvLp V P g g₀)
    (h : ∀ j, hasWeakWordDeriv Xt V I (f j) (g j)) : hasWeakWordDeriv Xt V I f₀ g₀ := by
  obtain ⟨hfm, hf₀, hft⟩ := hf
  obtain ⟨hgm, hg₀, hgt⟩ := hg
  let r : ℝ≥0∞ := (1 - P⁻¹)⁻¹
  have : ENNReal.HolderConjugate P r := S.holderConjugate_complement P Fact.out
  have : Fact (1 ≤ r) := ⟨ENNReal.HolderConjugate.one_le r P⟩
  have key := S.hasWeakWordDeriv_lp_limit V Xt hXt I P r (fun j => (hfm j).toLp (f j))
    (fun j => (hgm j).toLp (g j)) (hf₀.toLp f₀) (hg₀.toLp g₀)
    (Filter.Eventually.of_forall fun j =>
      S.hasWeakWordDeriv_congr_ae Xt V (h j) (hfm j).coeFn_toLp.symm (hgm j).coeFn_toLp.symm)
    hft hgt
  exact S.hasWeakWordDeriv_congr_ae Xt V key hf₀.coeFn_toLp hg₀.coeFn_toLp

/-- **Distributional convergence of integrals against tests**:
`L^P(V)` convergence gives convergence of `∫_V f_j ψ` for every test `ψ`. -/
theorem ConvLp.tendsto_integral_mul_test {f : ℕ → (Fin N → ℝ) → ℝ} {g : (Fin N → ℝ) → ℝ}
    (h : ConvLp V P f g) (ψ : TestFunction V ℝ (⊤ : ℕ∞)) :
    Tendsto (fun j => ∫ x in (V : Set (Fin N → ℝ)), f j x * ψ x) atTop
      (𝓝 (∫ x in (V : Set (Fin N → ℝ)), g x * ψ x)) := by
  obtain ⟨hf, hg, ht⟩ := convLp_iff.1 h
  let r : ℝ≥0∞ := (1 - P⁻¹)⁻¹
  have : ENNReal.HolderConjugate P r := S.holderConjugate_complement P Fact.out
  have : Fact (1 ≤ r) := ⟨ENNReal.HolderConjugate.one_le r P⟩
  exact S.tendsto_testIntegral_of_tendsto_eLpNorm V P r ψ f g hf hg ht

/-- **The weak extension limit** (BB
pp. 564–568). Let `u ∈ W^{kk,P}_{X̃,0}(V)` (the closure of the tests, `memSobolevXZero`) with
weak jet `D`. Suppose the identity `X̃_I (L φ) = R φ` holds weakly for every test `φ`, and the two
sides, which are bounded operators of the jet (cf. `ConvLp.actLp`), converge in `L^P(V)`, to `L₀`
and `R₀`, along every sequence of tests that approximates the jet. Then `X̃_I L₀ = R₀` weakly on `V`
(an identity in distributions between `L^P` functions). -/
theorem weakExtension_limit {w : Fin k → ℕ+}
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (V : Set (Fin N → ℝ)))
    (hfin : volume (V : Set (Fin N → ℝ)) < ⊤) {kk : ℕ} {u : (Fin N → ℝ) → ℝ}
    (hu : memSobolevXZero w Xt V kk P u) {D : List (Fin k) → (Fin N → ℝ) → ℝ}
    (hD : IsWeakJet w Xt V kk P u D) (I : List (Fin k))
    (L R : TestFunction V ℝ (⊤ : ℕ∞) → (Fin N → ℝ) → ℝ) (L₀ R₀ : (Fin N → ℝ) → ℝ)
    (hL : ∀ φ : ℕ → TestFunction V ℝ (⊤ : ℕ∞),
      (∀ K ∈ wordFamily w kk,
        ConvLp V P (fun j => wordDerivative Xt K (φ j : (Fin N → ℝ) → ℝ)) (D K)) →
      ConvLp V P (fun j => L (φ j)) L₀)
    (hR : ∀ φ : ℕ → TestFunction V ℝ (⊤ : ℕ∞),
      (∀ K ∈ wordFamily w kk,
        ConvLp V P (fun j => wordDerivative Xt K (φ j : (Fin N → ℝ) → ℝ)) (D K)) →
      ConvLp V P (fun j => R (φ j)) R₀)
    (h : ∀ φ : TestFunction V ℝ (⊤ : ℕ∞), hasWeakWordDeriv Xt V I (L φ) (R φ)) :
    hasWeakWordDeriv Xt V I L₀ R₀ := by
  obtain ⟨φ, hφ⟩ := exists_testSeq_convLp_jet hXt hfin hu hD
  exact hasWeakWordDeriv_of_convLp hXt I (hL φ hφ) (hR φ hφ) fun j => h (φ j)

end Limit

end RothschildStein.P1
