-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.GlobalSecondWordFromHalfRadius
public import RothschildStein.H3.GlobalFirstWordFromSecondWords
public import RothschildStein.H3.SobolevSecondNormBound

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory TopologicalSpace
open scoped ENNReal BigOperators
variable {n q : ℕ}

/-- A uniform coefficient for the global regularity estimate. -/
def globalRegularityConstant (q : ℕ) (K cE : ℝ) : ℝ :=
  1 + (wordFamily (driftWeight (q := q)) 2).card *
    (1 + (driftSecondWordFamily q).card * K / 2 + 2 * cE + K)

/-- Repaired global regularity, from the exact local regularity,
operator representative, half-radius and Phi interpolation inputs.
All global weak derivatives and the fixed Sobolev norm bound are constructed. -/
theorem global_regularity_of_halfRadius_and_interpolation
    (G : HomogeneousGroup n) (ν : G2.HomogeneousNorm G)
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    (K cE δE : ℝ) (hK : 0 ≤ K) (hcE : 0 ≤ cE) (hδE : 0 < δE)
    (hest : HalfRadiusEstimate G ν X p K)
    {u g : (Fin n → ℝ) → ℝ} (hu : MemLp u p (volume : Measure (Fin n → ℝ)))
    (hg : MemLp g p (volume : Measure (Fin n → ℝ)))
    (hlocal : ∀ R : ℝ, 0 < R →
      memSobolevX driftWeight X (quasiballDomain G ν 0 R) 2 p u ∧
      ∃ D : WeakDriftOperatorData X (quasiballDomain G ν 0 R) p u,
        D.operator =ᵐ[volume.restrict (G2.gaugeBall G ν 0 R)] g)
    (hinterp : ZeroCenteredPhiInterpolation G ν X p u cE δE) :
    memSobolevX driftWeight X ⊤ 2 p u ∧
      sobolevXENorm driftWeight X ⊤ 2 p u ≤
        ENNReal.ofReal (globalRegularityConstant q K cE) * (eLpNorm u p volume + eLpNorm g p volume) := by
  let U := (eLpNorm u p volume).toReal
  let F := (eLpNorm g p volume).toReal
  let B := K * F
  let A := (driftSecondWordFamily q).card * B / 2 + 2 * cE * U
  let M := U + A + B
  have hU : 0 ≤ U := ENNReal.toReal_nonneg
  have hF : 0 ≤ F := ENNReal.toReal_nonneg
  have hB : 0 ≤ B := mul_nonneg hK hF
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hsecond := exists_global_secondWord_of_halfRadiusEstimate G ν X hp hpt K hK hest hu hg hlocal
  have hfirst := exists_global_firstWord_of_secondWords_and_interpolation G ν X hp hpt hu
    (fun R hR => (hlocal R hR).1) B hB hsecond cE δE hcE hδE hinterp
  have hnil : hasWeakWordDeriv X ⊤ [] u u :=
    S.hasWeakWordDeriv_nil X ⊤ ((hu.locallyIntegrable hp).locallyIntegrableOn _)
  have hmembers : memSobolevX driftWeight X ⊤ 2 p u := by
    refine ⟨by simpa only [Opens.coe_top, Measure.restrict_univ] using hu, ?_⟩
    intro I hI
    have hw := (S.mem_wordFamily_iff driftWeight 2 I).mp hI
    have hc : wordWeight driftWeight I = 0 ∨ wordWeight driftWeight I = 1 ∨ wordWeight driftWeight I = 2 := by omega
    rcases hc with h0 | h1 | h2
    · rw [word_eq_nil_of_weight_zero driftWeight I h0]
      exact ⟨u, hnil, by simpa only [Opens.coe_top, Measure.restrict_univ] using hu⟩
    · obtain ⟨i, rfl⟩ := drift_word_weight_one I h1
      obtain ⟨d, hd, hdp, _⟩ := hfirst i
      exact ⟨d, hd, by simpa only [Opens.coe_top, Measure.restrict_univ] using hdp⟩
    · obtain ⟨d, hd, hdp, _⟩ := hsecond I h2
      exact ⟨d, hd, by simpa only [Opens.coe_top, Measure.restrict_univ] using hdp⟩
  have hb : ∀ I ∈ wordFamily driftWeight 2, weakWordENorm X ⊤ I p u ≤ ENNReal.ofReal M := by
    intro I hI
    have hw := (S.mem_wordFamily_iff driftWeight 2 I).mp hI
    have hc : wordWeight driftWeight I = 0 ∨ wordWeight driftWeight I = 1 ∨ wordWeight driftWeight I = 2 := by omega
    rcases hc with h0 | h1 | h2
    · rw [word_eq_nil_of_weight_zero driftWeight I h0, S.weakWordENorm_eq X ⊤ [] p u u hnil]
      simp only [Opens.coe_top, Measure.restrict_univ]
      rw [← ENNReal.ofReal_toReal hu.eLpNorm_ne_top]
      exact ENNReal.ofReal_le_ofReal (by dsimp only [M]; linarith)
    · obtain ⟨i, rfl⟩ := drift_word_weight_one I h1
      obtain ⟨d, hd, _, hdn⟩ := hfirst i
      rw [S.weakWordENorm_eq X ⊤ [i.succ] p u d hd]
      simp only [Opens.coe_top, Measure.restrict_univ]
      exact hdn.trans (ENNReal.ofReal_le_ofReal (by change A ≤ M; dsimp only [M]; linarith))
    · obtain ⟨d, hd, _, hdn⟩ := hsecond I h2
      rw [S.weakWordENorm_eq X ⊤ I p u d hd]
      simp only [Opens.coe_top, Measure.restrict_univ]
      exact hdn.trans (ENNReal.ofReal_le_ofReal (by change B ≤ M; dsimp only [M]; linarith))
  have hs := Finset.sum_le_sum (s := wordFamily driftWeight 2) hb
  have hn : sobolevXENorm driftWeight X ⊤ 2 p u ≤
      ENNReal.ofReal ((wordFamily (driftWeight (q := q)) 2).card * M) := by
    simpa only [sobolevXENorm, Finset.sum_const, nsmul_eq_mul,
      ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast] using hs
  have hcoef : (wordFamily (driftWeight (q := q)) 2).card * M ≤ globalRegularityConstant q K cE * (U + F) := by
    have ha : 0 ≤ 1 + 2 * cE := by positivity
    have hc : 0 ≤ (driftSecondWordFamily q).card * K / 2 + K := by positivity
    have hj : (0 : ℝ) ≤ (wordFamily (driftWeight (q := q)) 2).card := Nat.cast_nonneg _
    dsimp only [M, A, B]
    unfold globalRegularityConstant
    nlinarith [mul_nonneg (mul_nonneg hj ha) hF, mul_nonneg (mul_nonneg hj hc) hU]
  have hC : 0 ≤ globalRegularityConstant q K cE := by unfold globalRegularityConstant; positivity
  have he : ENNReal.ofReal (globalRegularityConstant q K cE * (U + F)) =
      ENNReal.ofReal (globalRegularityConstant q K cE) * (eLpNorm u p volume + eLpNorm g p volume) := by
    rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_add hU hF,
      ENNReal.ofReal_toReal hu.eLpNorm_ne_top, ENNReal.ofReal_toReal hg.eLpNorm_ne_top]
  exact ⟨hmembers, hn.trans ((ENNReal.ofReal_le_ofReal hcoef).trans_eq he)⟩

end RothschildStein.H3
