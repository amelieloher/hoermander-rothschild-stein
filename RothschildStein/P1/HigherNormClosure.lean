-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.GainExtension
public import RothschildStein.P1.SCommutation
public import RothschildStein.S.WeakSub
public import RothschildStein.S.SobolevAE
public import RothschildStein.S.TestSobolev
public import RothschildStein.Definitions.memSobolevXZero

/-!
# Higher-order gain: passing the commuted identities from tests to `W^{k,p}_{X̃,0}`

The functional-analytic half of the proof of the higher-order gain `‖S f‖_{W^{k,p}_{X̃}} ≤ C ‖f‖_{W^{k,p}_{X̃}}` (BB pp. 567–568,
Prop 11.31: "Sobolev approximation ... extend to the spaces stated"), independent of the operator algebra.

Let `A` and `B I J` (`I, J` words) be bounded operators on `L^P(V)` such that, for every test `φ`
and every word `I` of length at most `k` (weights one), the weak `X̃_I`-derivative of `A φ` is the
finite sum `∑_{|J| ≤ |I|} B I J (X̃_J φ)` (the commuted identities on tests).  Then for every
`f ∈ L^P(V) ∩ W^{k,P}_{X̃,0}(V)` (`memSobolevXZero`) and weak derivatives `g J` of `f`:

* `hasWeakWordDeriv_family_extension`: the weak `X̃_I`-derivative of `A f` is
  `∑_{|J| ≤ |I|} B I J (g J)` (closedness of the weak-derivative graph, as in BB Prop 2.5, for the `L^P`-limit of
  the identities along an approximating sequence of tests, BB Thm 2.9);
* `sobolevXENorm_family_extension_le`: `A f ∈ W^{k,P}_{X̃}(V)` and
  `‖A f‖_{W^{k,P}} ≤ (∑_I ∑_J ‖B I J‖) ‖f‖_{W^{k,P}}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal Topology
namespace RothschildStein.P1

section Words

variable {k : ℕ} {w : Fin k → ℕ+}

/-- Without drift (all weights one) the weight of a word is its length. -/
theorem wordWeight_eq_length_of_weights_one (hw : ∀ j, (w j : ℕ) = 1) (I : List (Fin k)) :
    wordWeight w I = I.length := by
  induction I with
  | nil => simp [wordWeight]
  | cons i I ih =>
    simp only [wordWeight, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    rw [hw i, ih]
    omega

/-- Without drift the word family `wordFamily` of order `n` consists of the words of length at
most `n`. -/
theorem mem_wordFamily_iff_length_le (hw : ∀ j, (w j : ℕ) = 1) (n : ℕ) (I : List (Fin k)) :
    I ∈ wordFamily w n ↔ I.length ≤ n := by
  rw [S.mem_wordFamily_iff, wordWeight_eq_length_of_weights_one hw]

/-- Words of length at most `n ≤ m` lie in the word family `wordFamily` of order `m`. -/
theorem mem_wordFamily_of_mem_wordsUpTo (hw : ∀ j, (w j : ℕ) = 1) {n m : ℕ} (hnm : n ≤ m)
    {J : List (Fin k)} (hJ : J ∈ wordsUpTo k n) : J ∈ wordFamily w m :=
  (mem_wordFamily_iff_length_le hw m J).2 ((mem_wordsUpTo.1 hJ).trans hnm)

end Words

section Closure

variable {N k : ℕ} {w : Fin k → ℕ+} {Xt : Fin k → (Fin N → ℝ) → (Fin N → ℝ)}
  {V : Opens (Fin N → ℝ)}

/-- The test obtained from a test by the empty word is the test itself. -/
theorem wordDerivativeTest_nil_eq
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (V : Set (Fin N → ℝ)))
    (φ : TestFunction V ℝ (⊤ : ℕ∞)) : S.wordDerivativeTest V Xt hXt [] φ = φ :=
  DFunLike.ext _ _ fun _ => rfl

/-- **Simultaneous `L^P`-limits keep a weak word derivative** (closedness of the
weak-derivative graph, as in BB Prop 2.5), for sequences. -/
theorem hasWeakWordDeriv_lp_tendsto
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (V : Set (Fin N → ℝ))) {P : ℝ≥0∞} [Fact (1 ≤ P)]
    (I : List (Fin k)) (u v : ℕ → Lp ℝ P (volume.restrict (V : Set (Fin N → ℝ))))
    (u₀ v₀ : Lp ℝ P (volume.restrict (V : Set (Fin N → ℝ))))
    (h : ∀ j, hasWeakWordDeriv Xt V I (u j) (v j))
    (hu : Tendsto u atTop (𝓝 u₀)) (hv : Tendsto v atTop (𝓝 v₀)) :
    hasWeakWordDeriv Xt V I u₀ v₀ := by
  let r : ℝ≥0∞ := (1 - P⁻¹)⁻¹
  have : ENNReal.HolderConjugate P r := S.holderConjugate_complement P Fact.out
  have : Fact (1 ≤ r) := ⟨ENNReal.HolderConjugate.one_le r P⟩
  exact S.hasWeakWordDeriv_lp_limit V Xt hXt I P r u v u₀ v₀ (Eventually.of_forall h) hu hv

/-- The `L^P` distance between a weak derivative `g` of `f` and the classical derivative of a
test `φ` is at most the `W^{kk,P}_{X̃}` distance `‖f - φ‖`, for a word of the family. -/
theorem eLpNorm_sub_wordDerivativeTest_le
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (V : Set (Fin N → ℝ))) {P : ℝ≥0∞} (kk : ℕ)
    {f g : (Fin N → ℝ) → ℝ} (J : List (Fin k)) (hJ : J ∈ wordFamily w kk)
    (hg : hasWeakWordDeriv Xt V J f g) (φ : TestFunction V ℝ (⊤ : ℕ∞)) :
    eLpNorm (fun x => g x - S.wordDerivativeTest V Xt hXt J φ x) P
        (volume.restrict (V : Set (Fin N → ℝ))) ≤
      sobolevXENorm w Xt V kk P (fun x => f x - φ x) := by
  have h1 : hasWeakWordDeriv Xt V J (fun x => f x - φ x)
      (fun x => g x - S.wordDerivativeTest V Xt hXt J φ x) :=
    S.hasWeakWordDeriv_sub Xt V hXt hg
      (S.hasWeakWordDeriv_classical V Xt hXt J φ φ.contDiff.contDiffOn)
  rw [← S.weakWordENorm_eq Xt V J P _ _ h1]
  unfold sobolevXENorm
  exact Finset.single_le_sum
    (f := fun I => weakWordENorm Xt V I P (fun x => f x - φ x)) (fun _ _ => zero_le) hJ

/-- **Convergence of the classical derivatives of an approximating sequence**: if tests `φ j`
converge to `f` in `W^{kk,P}_{X̃}(V)`, then for every word `J` of the family the classical
derivatives `X̃_J (φ j)` converge in `L^P(V)` to any weak derivative `g` of `f`. -/
theorem tendsto_testToLp_wordDerivativeTest
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (V : Set (Fin N → ℝ)))
    (hfin : volume (V : Set (Fin N → ℝ)) < ⊤) {P : ℝ≥0∞} [Fact (1 ≤ P)] (kk : ℕ)
    {f : (Fin N → ℝ) → ℝ} (φ : ℕ → TestFunction V ℝ (⊤ : ℕ∞))
    (hφ : Tendsto (fun j => sobolevXENorm w Xt V kk P (fun x => f x - φ j x)) atTop (𝓝 0))
    (J : List (Fin k)) (hJ : J ∈ wordFamily w kk)
    (g : Lp ℝ P (volume.restrict (V : Set (Fin N → ℝ)))) (hg : hasWeakWordDeriv Xt V J f g) :
    Tendsto (fun j => testToLp V hfin P (S.wordDerivativeTest V Xt hXt J (φ j))) atTop (𝓝 g) := by
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hφ (fun _ => zero_le)
    (fun j => ?_)
  have hae : (⇑(testToLp V hfin P (S.wordDerivativeTest V Xt hXt J (φ j))) - ⇑g) =ᵐ[volume.restrict
      (V : Set (Fin N → ℝ))] -(fun x => g x - S.wordDerivativeTest V Xt hXt J (φ j) x) := by
    filter_upwards [(testFunction_memLp V hfin (S.wordDerivativeTest V Xt hXt J (φ j)) P).coeFn_toLp]
      with x hx
    have hx' : (testToLp V hfin P (S.wordDerivativeTest V Xt hXt J (φ j))) x =
        S.wordDerivativeTest V Xt hXt J (φ j) x := hx
    simp only [Pi.sub_apply, Pi.neg_apply, hx']
    ring
  rw [eLpNorm_congr_ae hae, eLpNorm_neg]
  exact eLpNorm_sub_wordDerivativeTest_le hXt kk J hJ hg (φ j)

variable (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (V : Set (Fin N → ℝ)))
  (hfin : volume (V : Set (Fin N → ℝ)) < ⊤) {P : ℝ≥0∞} [Fact (1 ≤ P)]
  (hw : ∀ j, (w j : ℕ) = 1) (kk : ℕ)
  (A : Lp ℝ P (volume.restrict (V : Set (Fin N → ℝ))) →L[ℝ]
    Lp ℝ P (volume.restrict (V : Set (Fin N → ℝ))))
  (B : List (Fin k) → List (Fin k) → (Lp ℝ P (volume.restrict (V : Set (Fin N → ℝ))) →L[ℝ]
    Lp ℝ P (volume.restrict (V : Set (Fin N → ℝ)))))
  (hAB : ∀ I ∈ wordFamily w kk, ∀ φ : TestFunction V ℝ (⊤ : ℕ∞),
    hasWeakWordDeriv Xt V I (⇑(A (testToLp V hfin P φ)))
      (⇑(∑ J ∈ wordsUpTo k I.length,
        B I J (testToLp V hfin P (S.wordDerivativeTest V Xt hXt J φ)))))

include hXt hfin hw hAB

/-- **The commuted identity passes from tests to `W^{kk,P}_{X̃,0}(V)`** (approximation by tests, BB Thm 2.9,
and closedness of the weak-derivative graph; BB pp. 567-568, Prop 11.31: "Sobolev
approximation ... extend to the spaces stated"). If the weak `X̃_I`-derivative of `A φ` is
`∑_{|J| ≤ |I|} B I J (X̃_J φ)` for every test `φ` and every word `I` of the family, then for every
`f ∈ L^P(V)` in `W^{kk,P}_{X̃,0}(V)` with weak derivatives `g J` (`J` in the family) the weak
`X̃_I`-derivative of `A f` is `∑_{|J| ≤ |I|} B I J (g J)`. -/
theorem hasWeakWordDeriv_family_extension
    (f : Lp ℝ P (volume.restrict (V : Set (Fin N → ℝ)))) (hf : memSobolevXZero w Xt V kk P (⇑f))
    (g : List (Fin k) → Lp ℝ P (volume.restrict (V : Set (Fin N → ℝ))))
    (hg : ∀ J ∈ wordFamily w kk, hasWeakWordDeriv Xt V J (⇑f) (⇑(g J)))
    (I : List (Fin k)) (hI : I ∈ wordFamily w kk) :
    hasWeakWordDeriv Xt V I (⇑(A f)) (⇑(∑ J ∈ wordsUpTo k I.length, B I J (g J))) := by
  obtain ⟨-, φ, hφ⟩ := hf
  have hsub : ∀ J ∈ wordsUpTo k I.length, J ∈ wordFamily w kk := fun J hJ =>
    mem_wordFamily_of_mem_wordsUpTo hw ((mem_wordFamily_iff_length_le hw kk I).1 hI) hJ
  have hnil := hg [] (S.nil_mem_wordFamily w kk)
  have hfg : f = g [] :=
    Lp.ext (S.hasWeakWordDeriv_unique Xt V hnil (S.hasWeakWordDeriv_nil Xt V hnil.1)).symm
  have hconv : ∀ J ∈ wordFamily w kk, Tendsto
      (fun j => testToLp V hfin P (S.wordDerivativeTest V Xt hXt J (φ j))) atTop (𝓝 (g J)) :=
    fun J hJ => tendsto_testToLp_wordDerivativeTest hXt hfin kk φ hφ J hJ (g J) (hg J hJ)
  have h0 : Tendsto (fun j => testToLp V hfin P (φ j)) atTop (𝓝 (g [])) := by
    have h := hconv [] (S.nil_mem_wordFamily w kk)
    have e : (fun j => testToLp V hfin P (S.wordDerivativeTest V Xt hXt [] (φ j))) =
        fun j => testToLp V hfin P (φ j) :=
      funext fun j => by rw [wordDerivativeTest_nil_eq hXt (φ j)]
    rwa [e] at h
  have hu : Tendsto (fun j => A (testToLp V hfin P (φ j))) atTop (𝓝 (A f)) := by
    rw [hfg]
    exact (A.continuous.tendsto _).comp h0
  have hv : Tendsto (fun j => ∑ J ∈ wordsUpTo k I.length,
      B I J (testToLp V hfin P (S.wordDerivativeTest V Xt hXt J (φ j)))) atTop
      (𝓝 (∑ J ∈ wordsUpTo k I.length, B I J (g J))) :=
    tendsto_finsetSum _ fun J hJ => ((B I J).continuous.tendsto _).comp (hconv J (hsub J hJ))
  exact hasWeakWordDeriv_lp_tendsto hXt I (fun j => A (testToLp V hfin P (φ j)))
    (fun j => ∑ J ∈ wordsUpTo k I.length,
      B I J (testToLp V hfin P (S.wordDerivativeTest V Xt hXt J (φ j))))
    (A f) (∑ J ∈ wordsUpTo k I.length, B I J (g J)) (fun j => hAB I hI (φ j)) hu hv

/-- **The commuted bound on `W^{kk,P}_{X̃,0}(V)`**: under the hypotheses of
`hasWeakWordDeriv_family_extension`, `A f ∈ W^{kk,P}_{X̃}(V)` and
`‖A f‖_{W^{kk,P}_{X̃}(V)} ≤ (∑_I ∑_{|J| ≤ |I|} ‖B I J‖) ‖f‖_{W^{kk,P}_{X̃}(V)}`
(`memSobolevX`, `sobolevXENorm`; weak derivatives identified by
`hasWeakWordDeriv_family_extension`). -/
theorem sobolevXENorm_family_extension_le
    (f : Lp ℝ P (volume.restrict (V : Set (Fin N → ℝ)))) (hf : memSobolevXZero w Xt V kk P (⇑f)) :
    memSobolevX w Xt V kk P (⇑(A f)) ∧
      sobolevXENorm w Xt V kk P (⇑(A f)) ≤
        ENNReal.ofReal (∑ I ∈ wordFamily w kk, ∑ J ∈ wordsUpTo k I.length, ‖B I J‖) *
          sobolevXENorm w Xt V kk P (⇑f) := by
  have hjets : ∀ J ∈ wordFamily w kk, ∃ gJ : Lp ℝ P (volume.restrict (V : Set (Fin N → ℝ))),
      hasWeakWordDeriv Xt V J (⇑f) (⇑gJ) := by
    intro J hJ
    obtain ⟨g, hg, hgm⟩ := hf.1.2 J hJ
    exact ⟨hgm.toLp g, S.hasWeakWordDeriv_congr_ae Xt V hg ae_eq_rfl hgm.coeFn_toLp.symm⟩
  choose! g hg using hjets
  have hweak := fun I hI => hasWeakWordDeriv_family_extension hXt hfin hw kk A B hAB f hf g hg I hI
  refine ⟨⟨Lp.memLp (A f), fun I hI => ⟨_, hweak I hI, Lp.memLp _⟩⟩, ?_⟩
  have hM : ∀ J ∈ wordFamily w kk,
      eLpNorm (⇑(g J)) P (volume.restrict (V : Set (Fin N → ℝ))) ≤
        sobolevXENorm w Xt V kk P (⇑f) := by
    intro J hJ
    rw [← S.weakWordENorm_eq Xt V J P (⇑f) (⇑(g J)) (hg J hJ)]
    exact Finset.single_le_sum (f := fun I => weakWordENorm Xt V I P ⇑f) (fun _ _ => zero_le) hJ
  have hI : ∀ I ∈ wordFamily w kk, weakWordENorm Xt V I P (⇑(A f)) ≤
      ENNReal.ofReal (∑ J ∈ wordsUpTo k I.length, ‖B I J‖) * sobolevXENorm w Xt V kk P (⇑f) := by
    intro I hI
    rw [S.weakWordENorm_eq Xt V I P _ _ (hweak I hI), ← Lp.enorm_def,
      ENNReal.ofReal_sum_of_nonneg (fun J _ => norm_nonneg _), Finset.sum_mul]
    simp only [ofReal_norm]
    refine (enorm_sum_le _ _).trans (Finset.sum_le_sum fun J hJ => ?_)
    calc ‖B I J (g J)‖ₑ ≤ ‖B I J‖ₑ * ‖g J‖ₑ := (B I J).le_opENorm _
      _ ≤ ‖B I J‖ₑ * sobolevXENorm w Xt V kk P (⇑f) := by
        rw [Lp.enorm_def]
        gcongr
        exact hM J (mem_wordFamily_of_mem_wordsUpTo hw
          ((mem_wordFamily_iff_length_le hw kk I).1 hI) hJ)
  calc sobolevXENorm w Xt V kk P ⇑(A f)
      = ∑ I ∈ wordFamily w kk, weakWordENorm Xt V I P ⇑(A f) := rfl
    _ ≤ ∑ I ∈ wordFamily w kk, ENNReal.ofReal (∑ J ∈ wordsUpTo k I.length, ‖B I J‖) *
          sobolevXENorm w Xt V kk P ⇑f := Finset.sum_le_sum hI
    _ = ENNReal.ofReal (∑ I ∈ wordFamily w kk, ∑ J ∈ wordsUpTo k I.length, ‖B I J‖) *
          sobolevXENorm w Xt V kk P ⇑f := by
        rw [ENNReal.ofReal_sum_of_nonneg
          (fun I _ => Finset.sum_nonneg fun J _ => norm_nonneg _), Finset.sum_mul]

end Closure

end RothschildStein.P1
