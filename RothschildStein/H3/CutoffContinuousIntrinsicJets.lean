-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.WeakCutoffLeibniz
public import RothschildStein.S.ContinuousTestProducts
public import RothschildStein.S.WeakIntrinsicWords

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.H3

/-- Local continuous weak jets produce globally continuous
compact intrinsic jets after localization by an actual interior test.
Every weighted word is covered; exterior input values are unrestricted.
The ordered Leibniz formula retains all multiplicities. -/
theorem cutoff_continuous_intrinsic_jets {N m : ℕ}
    (Ω : Opens (Fin N → ℝ)) (w : Fin m → ℕ+)
    (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (k : ℕ)
    (u : (Fin N → ℝ) → ℝ) (jet : List (Fin m) → (Fin N → ℝ) → ℝ)
    (hzero : jet [] = u)
    (hw : ∀ I, wordWeight w I ≤ k → hasWeakWordDeriv X Ω I u (jet I))
    (hc : ∀ I, wordWeight w I ≤ k → ContinuousOn (jet I) (Ω : Set (Fin N → ℝ)))
    (φ : TestFunction Ω ℝ (⊤ : ℕ∞)) :
    let J := fun I => S.leibnizWordValue X I jet φ
    J [] = (fun x => u x * φ x) ∧ ∀ I, wordWeight w I ≤ k →
      hasIntrinsicWordDeriv X ⊤ I (fun x => u x * φ x) (J I) ∧
      Continuous (J I) ∧ HasCompactSupport (J I) ∧ tsupport (J I) ⊆ tsupport φ := by
  let J := fun I => S.leibnizWordValue X I jet φ
  have hJ0 : J [] = (fun x => u x * φ x) := by
    funext x
    simp only [J, S.leibnizWordValue, S.leibnizSplits, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, wordDerivative, hzero, add_zero]
  have hlocal (i : Fin m) := (hX i).contDiffOn (s := (Ω : Set (Fin N → ℝ)))
  have hJw (I : List (Fin m)) (hI : wordWeight w I ≤ k) :
      hasWeakWordDeriv X ⊤ I (fun x => u x * φ x) (J I) :=
    hasWeakWordDeriv_cutoff_word_global X Ω hlocal I u jet hzero
      (fun L hL => hw L ((S.wordWeight_sublist_le w hL).trans hI)) φ
  have hJs (I : List (Fin m)) : tsupport (J I) ⊆ tsupport φ := by
    have hterm (p : List (Fin m) × List (Fin m)) :
        tsupport (fun x => jet p.1 x * wordDerivative X p.2 φ x) ⊆ tsupport φ :=
      tsupport_mul_subset_right.trans (S.tsupport_wordDerivative_subset X p.2 φ)
    have hsum (items : List (List (Fin m) × List (Fin m))) :
        tsupport (fun x => (items.map (fun p => jet p.1 x * wordDerivative X p.2 φ x)).sum) ⊆
          tsupport φ := by
      induction items with
      | nil => simp
      | cons p items ih =>
        exact (tsupport_add _ _).trans (union_subset (hterm p) ih)
    exact hsum (S.leibnizSplits I)
  have hJc (I : List (Fin m)) (hI : wordWeight w I ≤ k) : Continuous (J I) := by
    have hterm (p : List (Fin m) × List (Fin m)) (hp : p ∈ S.leibnizSplits I) :
        Continuous (fun x => jet p.1 x * wordDerivative X p.2 φ x) := by
      have hsub := (S.leibnizSplits_sublist I p hp).1
      exact S.continuous_mul_test_of_continuousOn Ω
        (hc _ ((S.wordWeight_sublist_le w hsub).trans hI))
        (S.wordDerivativeTest Ω X hlocal p.2 φ)
    have hsum (items : List (List (Fin m) × List (Fin m)))
        (ht : ∀ p ∈ items, Continuous (fun x => jet p.1 x * wordDerivative X p.2 φ x)) :
        Continuous (fun x => (items.map (fun p => jet p.1 x * wordDerivative X p.2 φ x)).sum) := by
      induction items with
      | nil => exact continuous_const
      | cons p items ih =>
        exact (ht p List.mem_cons_self).add
          (ih (fun v hv => ht v (List.mem_cons_of_mem p hv)))
    exact hsum (S.leibnizSplits I) hterm
  refine ⟨hJ0, ?_⟩
  intro I hI
  refine ⟨?_, hJc I hI,
    φ.hasCompactSupport.of_isClosed_subset (isClosed_tsupport _) (hJs I), hJs I⟩
  exact S.hasIntrinsicWordDeriv_of_continuous_weak_subwords ⊤ X
    (fun i => (hX i).contDiffOn) I (fun x => u x * φ x) J hJ0
    (fun L hL => hJw L ((S.wordWeight_sublist_le w hL).trans hI))
    (fun L hL => (hJc L ((S.wordWeight_sublist_le w hL).trans hI)).continuousOn)

end RothschildStein.H3
