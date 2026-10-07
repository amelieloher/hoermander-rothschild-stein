-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.DriftSecondWeakNorm
public import RothschildStein.H3.WeakHorizontalNorms
public import RothschildStein.H3.WeakWordWeightCases
public import RothschildStein.Definitions.sobolevXENorm

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory TopologicalSpace
open scoped ENNReal BigOperators

/-- The exact fixed second-order Sobolev norm is bounded by the
zero, horizontal and complete second norms with their finite word count. -/
theorem sobolevXENorm_le_second_norms {n q : ℕ}
    (X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (Ω : Opens (Fin n → ℝ)) (p : ℝ≥0∞) (u : (Fin n → ℝ) → ℝ)
    (hu : memSobolevX driftWeight X Ω 2 p u) :
    sobolevXENorm driftWeight X Ω 2 p u ≤ (wordFamily (driftWeight (q := q)) 2).card *
      (eLpNorm u p (volume.restrict (Ω : Set (Fin n → ℝ)))+
        horizontalWeakENorm X Ω p u+driftSecondWeakENorm X Ω p u) := by
  classical
  have hz : weakWordENorm X Ω [] p u = eLpNorm u p (volume.restrict (Ω : Set (Fin n → ℝ))) := by
    obtain ⟨g,hg,_⟩ := hu.2 [] (by simp [S.mem_wordFamily_iff,wordWeight])
    exact S.weakWordENorm_eq X Ω [] p u u (S.hasWeakWordDeriv_nil X Ω hg.1)
  have hb : ∀ I ∈ wordFamily driftWeight 2, weakWordENorm X Ω I p u ≤
      eLpNorm u p (volume.restrict (Ω : Set (Fin n → ℝ)))+
        horizontalWeakENorm X Ω p u+driftSecondWeakENorm X Ω p u := by
    intro I hI
    have hw := (S.mem_wordFamily_iff driftWeight 2 I).mp hI
    have hc : wordWeight driftWeight I = 0 ∨ wordWeight driftWeight I = 1 ∨
        wordWeight driftWeight I = 2 := by omega
    rcases hc with h0 | h1 | h2
    · rw [word_eq_nil_of_weight_zero driftWeight I h0,hz]
      exact le_self_add.trans le_self_add
    · obtain ⟨i,rfl⟩ := drift_word_weight_one I h1
      have hh : weakWordENorm X Ω [i.succ] p u ≤ horizontalWeakENorm X Ω p u := by
        unfold horizontalWeakENorm
        exact Finset.single_le_sum (f := fun j : Fin q => weakWordENorm X Ω [j.succ] p u) (fun _ _ => bot_le) (Finset.mem_univ i)
      exact hh.trans (le_add_self.trans le_self_add)
    · have hs : weakWordENorm X Ω I p u ≤ driftSecondWeakENorm X Ω p u := by
        unfold driftSecondWeakENorm
        exact Finset.single_le_sum (f := fun J => weakWordENorm X Ω J p u) (fun _ _ => bot_le) ((mem_driftSecondWordFamily_iff I).mpr h2)
      exact hs.trans le_add_self
  unfold sobolevXENorm
  exact (Finset.sum_le_sum hb).trans_eq (by simp only [Finset.sum_const,nsmul_eq_mul])

/-- The same fixed Sobolev bound in real norms; finiteness follows
from actual Sobolev membership, with no additional norm hypothesis. -/
theorem sobolevXENorm_toReal_le_second_norms {n q : ℕ}
    (X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (Ω : Opens (Fin n → ℝ)) (p : ℝ≥0∞) (u : (Fin n → ℝ) → ℝ)
    (hu : memSobolevX driftWeight X Ω 2 p u) :
    (sobolevXENorm driftWeight X Ω 2 p u).toReal ≤
      ((wordFamily (driftWeight (q := q)) 2).card : ℝ)*
        ((eLpNorm u p (volume.restrict (Ω : Set (Fin n → ℝ)))).toReal+
          (horizontalWeakENorm X Ω p u).toReal+(driftSecondWeakENorm X Ω p u).toReal) := by
  have hh := (horizontalWeakENorm_lt_top X Ω p u hu).ne
  have hs := (driftSecondWeakENorm_lt_top X Ω p u hu).ne
  have hb := sobolevXENorm_le_second_norms X Ω p u hu
  have hU := hu.1.eLpNorm_ne_top
  have hUH := ENNReal.add_ne_top.mpr ⟨hU, hh⟩
  have hUHS := ENNReal.add_ne_top.mpr ⟨hUH, hs⟩
  have hcard : ((wordFamily (driftWeight (q := q)) 2).card : ℝ≥0∞) ≠ ⊤ := by simp
  have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top hcard hUHS) hb
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_add hUH hs, ENNReal.toReal_add hU hh] at hr
  exact hr

end RothschildStein.H3
