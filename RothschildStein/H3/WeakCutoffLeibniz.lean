-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.SobolevGlobalCutoff
public import RothschildStein.S.WordLeibniz

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory TopologicalSpace
namespace RothschildStein.H3
variable {N q : ℕ}

/-- A local weak identity with compact input strictly inside the
domain becomes a global identity for its actual jet when that jet also
vanishes outside the domain. -/
theorem hasWeakWordDeriv_globalize_of_compact_support
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)) (Ω : Opens (Fin N → ℝ))
    (I : List (Fin q)) {f g : (Fin N → ℝ) → ℝ}
    (h : hasWeakWordDeriv X Ω I f g) (hcf : HasCompactSupport f)
    (hs : tsupport f ⊆ (Ω : Set (Fin N → ℝ)))
    (hg : ∀ x, x ∉ (Ω : Set (Fin N → ℝ)) → g x = 0) :
    hasWeakWordDeriv X ⊤ I f g := by
  let K : Compacts (Fin N → ℝ) := ⟨tsupport f, hcf.isCompact⟩
  have hf0 : ∀ x, x ∉ (Ω : Set (Fin N → ℝ)) → f x = 0 :=
    fun x hx => image_eq_zero_of_notMem_tsupport (fun hh => hx (hs hh))
  have he := S.hasWeakWordDeriv_zeroExtension X ⊤ Ω (subset_univ _) K hs I f g h
    (Eventually.of_forall fun x _ hx => image_eq_zero_of_notMem_tsupport hx)
  have hif : (Ω : Set (Fin N → ℝ)).indicator f = f := by
    funext x
    by_cases hx : x ∈ (Ω : Set (Fin N → ℝ))
    · exact indicator_of_mem hx f
    · rw [indicator_of_notMem hx, hf0 x hx]
  have hig : (Ω : Set (Fin N → ℝ)).indicator g = g := by
    funext x
    by_cases hx : x ∈ (Ω : Set (Fin N → ℝ))
    · exact indicator_of_mem hx g
    · rw [indicator_of_notMem hx, hg x hx]
  simpa only [hif, hig] using he

/-- The full ordered-word cutoff formula is valid globally,
using local weak subword jets and the actual global cutoff derivatives.
Repeated letters retain their multiplicities (BB p. 73). -/
theorem hasWeakWordDeriv_cutoff_word_global
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)) (Ω : Opens (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin N → ℝ)))
    (I : List (Fin q)) (f : (Fin N → ℝ) → ℝ)
    (F : List (Fin q) → (Fin N → ℝ) → ℝ) (hF0 : F [] = f)
    (hF : ∀ J, J.Sublist I → hasWeakWordDeriv X Ω J f (F J))
    (φ : TestFunction Ω ℝ (⊤ : ℕ∞)) :
    hasWeakWordDeriv X ⊤ I (fun x => f x * φ x)
      (S.leibnizWordValue X I F φ) := by
  apply hasWeakWordDeriv_globalize_of_compact_support X Ω I
    (S.hasWeakWordDeriv_mul_word X Ω hX I f φ φ.contDiff.contDiffOn F hF0 hF)
    φ.hasCompactSupport.mul_left (tsupport_mul_subset_right.trans φ.tsupport_subset)
  intro x hx
  have hz (J : List (Fin q)) : wordDerivative X J φ x = 0 :=
    image_eq_zero_of_notMem_tsupport
      (fun hh => hx (φ.tsupport_subset (S.tsupport_wordDerivative_subset X J φ hh)))
  simp only [S.leibnizWordValue]
  have he : ((S.leibnizSplits I).map
      (fun p => F p.1 x * wordDerivative X p.2 φ x)) =
      (S.leibnizSplits I).map (fun _ => (0 : ℝ)) := by
    apply List.map_congr_left
    intro p _
    rw [hz, mul_zero]
  rw [he]
  simp

end RothschildStein.H3
